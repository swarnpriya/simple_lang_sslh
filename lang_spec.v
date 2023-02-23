Require Import Nat.
Require Import String.
Require Import List.
Require Import Coq.Init.Datatypes PArray.
From mathcomp Require Import all_ssreflect all_algebra.
From LF Require Export lang.

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
(* x := a[i]  
   x := protect(x) 
   a[j] := x *)

(* Instructions *)
Inductive instr : Type :=
| Iassgn : var -> expr -> instr (* assignemnt x := e *)
| Iload : var -> arr_access -> instr (* x := a[e] *)
| Istore : arr_access -> expr -> instr  (* a[e] := e *) 
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
  {| scmd := (if bf then i1 else i2) ++ c; 
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
     ms := s.(ms) |}
(* y represents the correct value stored in that variable *)
| Iprotect_sem_spec : forall s x y c,
  s.(scmd) = Iprotect x y :: c ->
  sem_instr_spec s Dstep Lempty 
  {| scmd := c; 
     rmap := if s.(ms) then update_rmap s.(rmap) x 0 else update_rmap s.(rmap) x (s.(rmap) y);
     mmap := s.(mmap);
     ms := s.(ms) |}.


(* Multi step for instructions with spec *)
Inductive multi_step_spec : state -> seq directive -> seq leakage -> nat -> state -> Prop :=
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



















