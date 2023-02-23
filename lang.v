Require Import Nat.
Require Import String.
Require Import List.
Require Import Coq.Init.Datatypes PArray.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.

(********************************************************)

(* Syntax of language *)

(********************************************************)

(* Value *)

Definition value := nat.

(* Operators *)
Inductive bop : Type :=
| plus : bop
| minus : bop.

(* Boolean Operators *)
Inductive bool_op : Type :=
| equal : bool_op
| less_than : bool_op
| greater_than : bool_op.

Definition varr := string.
Definition var  := string.

(* Expressions *)
Inductive expr : Type :=
| Evar : var -> expr (* variable *)
| Ebop : bop -> expr -> expr -> expr (* operation *).

(* Boolean Expressions *)
Inductive bexpr : Type :=
| Ebool : bool_op -> expr -> expr -> bexpr.

Inductive arr_access : Type :=
| AA : varr -> expr -> arr_access (* a[e] *).

(* Instructions *)
Inductive instr : Type :=
| Iassgn : var -> expr -> instr (* assignemnt x := e *)
| Iload : var -> arr_access -> instr (* x := a[e] *)
| Istore : arr_access -> expr -> instr  (* a[e] := e *) 
| Iif : bexpr -> seq instr -> seq instr -> instr (* conditional if b i i *).

Definition cmd := seq instr.

Definition map (A:Type) := string -> A.

Definition get_map {A:Type} (m:map A) (x:string) := m x.


(*Parameter update_map : forall {A:Type}, map A -> string -> A -> map A.*)

Definition update_map {A:Type} (m:map A) x v : map A := 
  fun y => if String.eqb x y then v else m y.

(* Register map *)
(* Maps registers to values *)
Definition regmap : Type := map value.

(* Signature of Array *)
Module Array.
   Parameter t : Type.
   Parameter get : t -> value -> value.
   Parameter set : t -> nat -> value -> t.
   Parameter get_length : t -> nat.
End Array.


(* Memory *)
Definition mem : Type := map Array.t. 

(* State *)
Record state := State {
  scmd : cmd;
  rmap : regmap;
  mmap  : mem;
  ms : bool
}.

(* State with no speculation *)
Record state_sf := State_sf {
  scmd_sf : cmd;
  rmap_sf : regmap;
  mmap_sf  : mem
}.

Definition eval_bop (o:bop) (v:value) (v':value) : value :=
  match o with 
  | plus => v + v'
  | minus => v - v'
  end.

Definition eval_bool_op (o:bool_op) (v:value) (v':value) : bool :=
  match o with 
  | equal => v == v'
  | less_than => v < v'
  | greater_than => v > v'
  end.

(* Semantic of expressions *)
Fixpoint sem_expr_spec (s:state) (e:expr) : value :=
  match e with 
  | Evar x => (rmap s) x
  | Ebop o e e' => eval_bop o (sem_expr_spec s e) (sem_expr_spec s e')
  end.

(* Semantic of expressions *)
Fixpoint sem_expr (s:state_sf) (e:expr) : value :=
  match e with 
  | Evar x => (rmap_sf s) x
  | Ebop o e e' => eval_bop o (sem_expr s e) (sem_expr s e')
  end.

(*Definition with_stmt_spec (s:state) (i:instr) := 
  {| stmt := i; 
     rmap := s.(rmap); 
     mmap := s.(mmap); 
     ms := s.(ms) |}.

Definition with_stmt (s:state_sf) (i:instr) := 
  {| stmt_sf := i; 
     rmap_sf := s.(rmap_sf); 
     mmap_sf := s.(mmap_sf) |}.*)

Definition update_mem (m:mem) (a:varr) (n:nat) (v:value) := 
   let t := m a in
   let t' := Array.set t n v in
   update_map m a t'.

Definition update_rmap (r:regmap) (x:var) (v:value) :=
   update_map r x v.

Definition in_bound (m:mem) (a:varr) (i:nat) := 
  let av := m a in
  let n := Array.get_length av in 
  if i <= n then true else false.

(* Leakages *)
Inductive leakage : Type :=
| Lbool : bool -> leakage
| Lindex : nat -> leakage
| Lempty : leakage.

(* Directives *)
Inductive directive : Type :=
| Dstep : directive 
| Dforce : bool -> directive
| Dload : varr -> nat -> directive 
| Dstore : varr -> nat -> directive.

(* Semantics of instructions with speculation *)
Inductive sem_instr_spec : state -> directive -> leakage -> state -> Prop :=
| Iassgn_sem_spec : forall s x e c,
  s.(scmd) = Iassgn x e :: c ->  
  sem_instr_spec s Dstep Lempty 
  {| scmd := c; 
     rmap := update_rmap s.(rmap) x (sem_expr_spec s e);
     mmap := s.(mmap); 
     ms := s.(ms) |}
| Iif_sem_spec : forall s bop e1 e2 bf i1 i2 v1 v2 b' c,
  s.(scmd) = Iif (Ebool bop e1 e2) i1 i2 :: c ->
  sem_expr_spec s e1 = v1 ->
  sem_expr_spec s e2 = v2 -> 
  eval_bool_op bop v1 v2 = b' ->
  sem_instr_spec s (Dforce bf) (Lbool b') 
  {| scmd := if bf then i1 else i2 ++ c; 
     rmap := s.(rmap);
     mmap := s.(mmap); 
     ms := if b' == bf then s.(ms) else true (*s.ms || b' != bf*)|}
(* update the x in regmap with 0 in case of misspeculation *)
(* we don't need this rule because we will slh *)
(*| Ifload_sem : forall s x a e,
  s.(stmt) = Iload x (AA a e) ->
  sem_instr s (Dload a (sem_expr s e)) (Lindex (sem_expr s e)) {| stmt := Iempty; 
                              rmap := if s.(ms) 
                                      then update_rmap s.(rmap) x 0 
                                      else update_rmap s.(rmap) x (Array.get (s.(mmap) a) (sem_expr s e));
                              mmap := s.(mmap);
                              ms := s.(ms) |}*)
| Iload_sem_spec : forall s x a e c,
  s.(scmd) = Iload x (AA a e) :: c ->
  sem_instr_spec s (Dload a (sem_expr_spec s e)) (Lindex (sem_expr_spec s e)) 
  {| scmd := c; 
     rmap := update_rmap s.(rmap) x (Array.get (s.(mmap) a) (sem_expr_spec s e));
     mmap := s.(mmap);
     ms := s.(ms) |}
| Istore_sem_spec : forall s a e e' c,
  s.(scmd) = Istore (AA a e) e' :: c ->
  sem_instr_spec s (Dstore a (sem_expr_spec s e)) (Lindex (sem_expr_spec s e)) 
  {| scmd := c; 
     rmap := s.(rmap);
     mmap := update_mem s.(mmap) a (sem_expr_spec s e) (sem_expr_spec s e');
     ms := s.(ms) |}.

(* Semantics of instructions without speculation *)
Inductive sem_instr : state_sf -> leakage -> state_sf -> Prop :=
| Iassgn_sem : forall s x e c,
  s.(scmd_sf) = Iassgn x e :: c ->  
  sem_instr s Lempty 
  {| scmd_sf := c; 
     rmap_sf := update_rmap s.(rmap_sf) x (sem_expr s e);
     mmap_sf := s.(mmap_sf) |}
(*| Iif_sem_true : forall s i1 i2 bop e1 e2,
  s.(stmt) = Iif (Ebool bop e1 e2) i1 i2 ->
  eval_bool_op bop (sem_expr s e1) (sem_expr s e2) = true ->
  sem_instr s (Lbool true) (with_stmt s i1)
| Iif_sem_false : forall s i1 i2 bop e1 e2,
  s.(stmt) = Iif (Ebool bop e1 e2) i1 i2 ->
  eval_bool_op bop (sem_expr s e1) (sem_expr s e2) = false ->
  sem_instr s (Lbool false) (with_stmt s i2)*)
| Iif_sem : forall s i1 i2 bop e1 e2 c,
  s.(scmd_sf) = Iif (Ebool bop e1 e2) i1 i2 :: c ->
  sem_instr s (Lbool (eval_bool_op bop (sem_expr s e1) (sem_expr s e2))) 
  {| scmd_sf := (if (eval_bool_op bop (sem_expr s e1) (sem_expr s e2)) then i1 else i2) ++ c; 
     rmap_sf := s.(rmap_sf);
     mmap_sf := s.(mmap_sf) |}
| Iload_sem : forall s x a e c,
  s.(scmd_sf) = Iload x (AA a e) :: c ->
  sem_instr s (Lindex (sem_expr s e)) 
  {| scmd_sf := c; 
     rmap_sf := update_rmap s.(rmap_sf) x (Array.get (s.(mmap_sf) a) (sem_expr s e));
     mmap_sf := s.(mmap_sf)|}
| Istore_sem : forall s a e e' c,
  s.(scmd_sf) = Istore (AA a e) e' :: c ->
  sem_instr s (Lindex (sem_expr s e)) 
  {| scmd_sf := c; 
     rmap_sf := s.(rmap_sf);
     mmap_sf := update_mem s.(mmap_sf) a (sem_expr s e) (sem_expr s e') |}.
 
(* Multi step for instructions with spec *)
Inductive multi_step_spec : state -> seq directive -> seq leakage -> state -> Prop :=
| sem_empty_spec : forall s, multi_step_spec s nil nil s
| sem_seq_spec : forall s d l s' d' l' s'',
  sem_instr_spec s d l s' ->
  multi_step_spec s' d' l' s'' ->
  multi_step_spec s (d :: d') (l :: l') s''.

(* Multi step for instructions without spec *)
Inductive multi_step : state_sf -> seq leakage -> nat -> state_sf -> Prop :=
| sem_empty : forall s, multi_step s nil 0 s
| sem_seq : forall s l s' l' s'' n,
  sem_instr s l s' ->
  multi_step s' l' n s'' ->
  multi_step s (l :: l') (n + 1) s''.

Definition final_state (s:state_sf) : bool :=
match s.(scmd_sf) with 
| [::] => true
| _ => false
end.

(*Fixpoint inbound_instr (s:state_sf) (si:instr) {struct si}: Prop :=
match si with 
| Iassgn x e => True 
| Iload x (AA a e) => in_bound s.(mmap_sf) a (sem_expr s e) = true
| Istore (AA a e) e' => in_bound s.(mmap_sf) a (sem_expr s e) = true
| Iif b i i' => True
| Iseq i i' => inbound_instr s i /\ inbound_instr s i'
| Iempty => True
end.

Definition inbound_state (s:state_sf) : Prop :=
let si := s.(stmt_sf) in
inbound_instr s si.*)

Definition safe_state (s:state_sf) :=
final_state s = true \/ exists l s', sem_instr s l s'.


















