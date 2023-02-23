Require Import Nat.
Require Import String.
Require Import List.
Require Import Coq.Init.Datatypes PArray.
From mathcomp Require Import all_ssreflect all_algebra.
From LF Require Export lang_declassify.

Set Implicit Arguments.

(********************************************************)

(* Syntax of language *)

(********************************************************)

(* Example 1 *)
(* fn (length) {
   if (inbound(length) { //attacker can pass any value of length which might not be in bound
      x := a[length] ; //speculatively processor goes her...lead to access to unbound index (secret memory)
      a[y] := x;  // loads data from secret memory 
      for (i = 0 ; i <= length; i++) { //based on conditional
          a[i] := 0; // writes in secret memory
      }
   }
*)
(* During sequential execution, this is not a problem but it might be a problem in speculative execution *)
(* One solution is to put fence after line 2 but the drawback of fence is they stop speculation of 
   all instructions, not only the instructions that might leak *)
(* Another solution: protect ==> it only stops speculation along certain path, memory load is guarded by protect *)

(* Example 2 *)
(* x := a[i1]
   y := a[i2]
   z := x + y
   w := b[z] *)

(* Example 3: Use of protect : Protects all the public loads so that attacker doesn't use it to get the secret data *)
(* x := a[i] // where a is public and i is always public 
   a[j] := x // storing the value x in the memory *)
(* x := a[i]  x: Transient
   x := protect(x) RHS: x: Transient LHS: x: Public
   a[j] := x *)

(* Instructions *)
Inductive instr : Type :=
| Iempty : instr
| Iassgn : var -> declassify -> expr -> instr (* assignemnt x := d e *)
| Iload : var -> declassify -> arr_access -> instr (* x := d a[e] *)
| Istore : arr_access -> declassify -> expr -> instr  (* a[e] := d e *) 
| Iif : bexpr -> seq instr -> seq instr -> instr (* conditional if b i i *)
| Iprotect : var -> var -> instr (* we will protect the var which gets value from public load *).

Definition cmd := seq instr.

(* State *)
Record state := State {
  scmd : cmd;
  rmap : regmap;
  mmap  : mem;
  ms : bool
}.

(* Semantic of expressions *)
Fixpoint sem_expr_spec (s:state) (e:expr) : value :=
  match e with 
  | Evar x => (rmap s) x
  | Ebop o e e' => eval_bop o (sem_expr_spec s e) (sem_expr_spec s e')
  end.

(* Directives *)
Inductive directive : Type :=
| Dstep : directive 
| Dforce : bool -> directive
| Dload : varr -> nat -> directive 
| Dstore : varr -> nat -> directive.

(* Semantics of instructions with speculation *) 
Inductive sem_instr_spec : state -> directive -> seq leakage -> state -> Prop :=
| Iempty_sem_spec : forall s c,
  s.(scmd) = Iempty :: c ->
  sem_instr_spec s 
  Dstep 
  [::]
  {| scmd := c; rmap := rmap s; mmap := mmap s; ms := ms s |}
| Iassgn_sem_spec : forall s x d e c,
  s.(scmd) = Iassgn x d e :: c ->  
  sem_instr_spec s 
  Dstep 
  (if d then [:: Ldeclassify (Some (sem_expr_spec s e))] else [:: Lempty])
  {| scmd := c; 
     rmap := update_rmap s.(rmap) x (sem_expr_spec s e);
     mmap := s.(mmap); 
     ms := s.(ms) |}
| Iif_sem_spec : forall s bop e1 e2 bf i1 i2 v1 v2 b' c,
  s.(scmd) = Iif (Ebool bop e1 e2) i1 i2 :: c ->
  sem_expr_spec s e1 = v1 ->
  sem_expr_spec s e2 = v2 -> 
  eval_bool_op bop v1 v2 = b' ->
  sem_instr_spec s 
  (Dforce bf) 
  [::(Lbool b')] 
  {| scmd := (if bf then i1 else i2) ++ c; 
     rmap := s.(rmap);
     mmap := s.(mmap); 
     ms := if b' == bf then s.(ms) else true (*s.ms || b' != bf*)|}
| Iload_sem_spec : forall s x d a e c,
  s.(scmd) = Iload x d (AA a e) :: c ->
  sem_instr_spec s 
  (Dload a (sem_expr_spec s e)) 
  (if d then [:: Lindex (sem_expr_spec s e);
                 Ldeclassify (Some (Array.get (mmap s a) (sem_expr_spec s e)))]
        else [:: Lindex (sem_expr_spec s e)])
  {| scmd := c; 
     rmap := update_rmap s.(rmap) x (Array.get (s.(mmap) a) (sem_expr_spec s e));
     mmap := s.(mmap);
     ms := s.(ms) |}
| Istore_sem_spec : forall s a e d e' c,
  s.(scmd) = Istore (AA a e) d e' :: c ->
  sem_instr_spec s (Dstore a (sem_expr_spec s e))
  (if d then [:: Lindex (sem_expr_spec s e); Ldeclassify (Some (sem_expr_spec s e'))]
        else [:: Lindex (sem_expr_spec s e)])
  {| scmd := c; 
     rmap := s.(rmap);
     mmap := update_mem s.(mmap) a (sem_expr_spec s e) (sem_expr_spec s e');
     ms := s.(ms) |}
| Iprotect_sem_spec : forall s x y c,
  s.(scmd) = Iprotect x y :: c ->
  sem_instr_spec s 
  Dstep 
  [:: Lempty] 
  {| scmd := c; 
     rmap := if s.(ms) then update_rmap s.(rmap) x 0 else update_rmap s.(rmap) x (s.(rmap) y);
     mmap := s.(mmap);
     ms := s.(ms) |}.


(* Multi step for instructions with spec *)
Inductive multi_step_spec : state -> seq directive -> seq (seq leakage) -> nat -> state -> Prop :=
| sem_empty_spec : forall s, multi_step_spec s nil nil 0 s
| sem_seq_spec : forall s d l s' d' l' s'' n,
  sem_instr_spec s d l s' ->
  multi_step_spec s' d' l' n s'' ->
  multi_step_spec s (d :: d') (l :: l') (n + 1) s''.

Definition final_state_spec (s:state) : bool :=
match s.(scmd) with 
| [::] => true
| _ => false
end.


Definition safe_state (s:state) :=
final_state_spec s = true \/ exists d l s', sem_instr_spec s d l s'.

