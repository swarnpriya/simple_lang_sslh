Require Import Nat.
Require Import String.
Require Import List.
From mathcomp Require Import all_ssreflect all_algebra.
From LF Require Export lang type.

Set Implicit Arguments.

Inductive state_equiv (s1 s2:state_sf) (VGamma:venv) (AGamma:aenv) : Prop :=
| st_equiv : 
  (forall x, VGamma x = Some Public ->
   s1.(rmap_sf) x = s2.(rmap_sf) x) ->
  (forall a, AGamma a = Some Public ->
   s1.(mmap_sf) a = s2.(mmap_sf) a) ->
  s1.(scmd_sf) = s2.(scmd_sf) ->
  state_equiv s1 s2 VGamma AGamma.


Definition constant_time (VGamma:venv) (AGamma:aenv) (s1 s2:state_sf) := forall s1' s2' l1 l2 n,
state_equiv s1 s2 VGamma AGamma ->
multi_step s1 l1 n s1' ->
multi_step s2 l2 n s2' -> 
l1 = l2 /\ (safe_state s1' <-> safe_state s2').

Lemma progress : forall VGamma AGamma s,
type_cmd VGamma AGamma s.(scmd_sf) ->
safe_state s.
Proof.
move=> VGamma AGamma [] /= []. 
(* empty *)
+ by left.
(* i::c *)
move=> i c r m hty. induction hty. induction H.
(* x := e:: c*)
+ right.
  exists Lempty. 
  exists {| scmd_sf := c0; 
            rmap_sf := update_rmap r x 
                       (sem_expr {| scmd_sf := Iassgn x e :: c0; rmap_sf := r; mmap_sf := m |} e);
            mmap_sf := m |}.
  by apply Iassgn_sem.
(* x := a[e]::c *)
+ case: a H0=> a e H0. right.
  exists (Lindex (sem_expr {| scmd_sf := Iload x (AA a e) :: c0; rmap_sf := r; mmap_sf := m |} e)).
  exists {| scmd_sf := c0; 
            rmap_sf := update_rmap r x 
                       (Array.get (mmap_sf {| scmd_sf := Iload x (AA a e) :: c0; rmap_sf := r; mmap_sf := m |} a) 
                       (sem_expr {| scmd_sf := Iload x (AA a e) :: c0; rmap_sf := r; mmap_sf := m |} e));
            mmap_sf := m |}.
  by apply Iload_sem.
(* a[e] := e *)
+ case: a H0=> a ei H0. right. 
  exists (Lindex (sem_expr {| scmd_sf := Istore (AA a ei) e :: c0; rmap_sf := r; mmap_sf := m |} ei)).
  exists {| scmd_sf := c0; 
            rmap_sf := r;
            mmap_sf := update_mem m a 
                       (sem_expr {| scmd_sf := Istore (AA a ei) e :: c0; rmap_sf := r; mmap_sf := m |} ei) 
                       (sem_expr {| scmd_sf := Istore (AA a ei) e :: c0; rmap_sf := r; mmap_sf := m |} e) |}.  
  by apply Istore_sem. 
(* if b i1 i2 *)
+ case: b H=> b e1 e2 H. right.
  exists (Lbool (eval_bool_op b 
                (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i0 i' :: c0; rmap_sf := r; mmap_sf := m |} e1) 
                (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i0 i' :: c0; rmap_sf := r; mmap_sf := m |} e2))).
  exists {| scmd_sf := (if (eval_bool_op b (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i0 i' :: c0; rmap_sf := r; mmap_sf := m |} e1) 
                                             (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i0 i' :: c0; rmap_sf := r; mmap_sf := m |} e2)) 
                        then i0 
                        else i') ++ c0; 
            rmap_sf := r;
            mmap_sf := m |}.
  by apply Iif_sem.
by left. 
Qed.

Lemma union_public_eq : forall T T',
union_level T T' = Public ->
T = Public /\ T' = Public.
Proof.
unfold union_level. move=> T T'.
case: T=> //=.
Qed.

Lemma expr_equiv_val : forall VGamma s1 s2 e T,
(forall x ,VGamma x = Some Public ->
 s1.(rmap_sf) x = s2.(rmap_sf) x) ->
type_expr VGamma e T ->
T = Public ->
sem_expr s1 e = sem_expr s2 e.
Proof.
move=> VGamma [] st1 r1 m1 [] st2 r2 m2 e T /= hvar hty hteq.
induction hty.
+ rewrite hteq in H. rewrite /=. by move: (hvar x H)=> ->.
apply union_public_eq in hteq. case: hteq=> h1 h2.
case: o=> //=;move: (IHhty1 h1) => ->; by move: (IHhty2 h2) => ->.
Qed.

(* Because our language design is safe: it never goes to a stuck state *)
(* In speculative semantic it might be diff *)
Lemma safe_lang : forall s,
safe_state s.
Proof.
rewrite /safe_state /= /final_state /=.
move=> [] st r m /=. case: st=> //=.
+ by left.
move=> i c. case: i.
(* x := e *)
+ move=> x e. right. exists Lempty. 
  exists {| scmd_sf := c; 
            rmap_sf := update_rmap r x 
                       (sem_expr {| scmd_sf := Iassgn x e :: c; rmap_sf := r; mmap_sf := m |} e);
            mmap_sf := m |}.
  by apply Iassgn_sem.
(* x := a[e]::c *)
+ move=> x [] a e. right.
  exists (Lindex (sem_expr {| scmd_sf := Iload x (AA a e) :: c; rmap_sf := r; mmap_sf := m |} e)).
  exists {| scmd_sf := c; 
            rmap_sf := update_rmap r x 
                       (Array.get (mmap_sf {| scmd_sf := Iload x (AA a e) :: c; rmap_sf := r; mmap_sf := m |} a) 
                       (sem_expr {| scmd_sf := Iload x (AA a e) :: c; rmap_sf := r; mmap_sf := m |} e));
            mmap_sf := m |}.
  by apply Iload_sem.
(* a[e] := e *)
+ move=> [] a ei. right. 
  exists (Lindex (sem_expr {| scmd_sf := Istore (AA a ei) e :: c; rmap_sf := r; mmap_sf := m |} ei)).
  exists {| scmd_sf := c; 
            rmap_sf := r;
            mmap_sf := update_mem m a 
                       (sem_expr {| scmd_sf := Istore (AA a ei) e :: c; rmap_sf := r; mmap_sf := m |} ei) 
                       (sem_expr {| scmd_sf := Istore (AA a ei) e :: c; rmap_sf := r; mmap_sf := m |} e) |}.  
  by apply Istore_sem. 
(* if b i1 i2 *)
+ move=> [] b e1 e2 i i'. right.
  exists (Lbool (eval_bool_op b 
                (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i i' :: c; rmap_sf := r; mmap_sf := m |} e1) 
                (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i i' :: c; rmap_sf := r; mmap_sf := m |} e2))).
  exists {| scmd_sf := (if (eval_bool_op b (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i i' :: c; rmap_sf := r; mmap_sf := m |} e1) 
                                             (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i i' :: c; rmap_sf := r; mmap_sf := m |} e2)) 
                        then i 
                        else i') ++ c; 
            rmap_sf := r;
            mmap_sf := m |}.
  by apply Iif_sem.
Qed.

Lemma sub_public_always_public : forall T,
sub_level T Public = true ->
T = Public.
Proof.
by move=> [] //=.
Qed.

Lemma union_public_always_public : forall T1 T2,
union_level T1 T2 = Public ->
T1 = Public /\ T2 = Public.
Proof.
by move=> [] [] //=.
Qed.

Lemma leakage_eq_n : forall s l n s',
multi_step s l n s' ->
size l = n.
Proof.
move=> [] st r m l n [] st' r' m' hmulti.
induction hmulti; auto.
by induction H;rewrite -cat1s size_cat /= IHhmulti add1n /= addn1. 
Qed.

Lemma type_concat : forall VGamma AGamma c1 c2,
type_cmd VGamma AGamma c1 ->
type_cmd VGamma AGamma c2 ->
type_cmd VGamma AGamma (c1 ++ c2).
Proof.
move=> VGamma AGamma c1 c2 hc1 hc2.
induction c1; rewrite /=.
+ by apply hc2.
inversion hc1; subst.
apply T_seq. 
+ by apply H1.  
apply IHc1. by apply H2.
Qed.

Lemma preservation : forall VGamma AGamma s1 l1 s1',
type_cmd VGamma AGamma s1.(scmd_sf) ->
sem_instr s1 l1 s1' ->
type_cmd VGamma AGamma s1'.(scmd_sf).
Proof.
move=> VGamma AGamma [] st r m l1 s1' hty hstep.
induction hstep.
+ rewrite /update_rmap /update_map /=. rewrite H in hty.
  by inversion hty.
+ rewrite H in hty. inversion hty; subst.
  inversion H2; subst.
  case: ifP=> //=.
  (* true *)
  + move=> htrue. by move: (type_concat H6 H3).
  (* false *)
  move=> hfalse. by move: (type_concat H7 H3).
+ rewrite /update_rmap /update_map /=. rewrite H in hty.
  by inversion hty.
rewrite /update_rmap /update_map /=. rewrite H in hty.
by inversion hty.
Qed.
   
Lemma type_prev_ct_step : forall VGamma AGamma s1 s2 s1' s2' l1 l2,
type_cmd VGamma AGamma s1.(scmd_sf) ->
state_equiv s1 s2 VGamma AGamma ->
sem_instr s1 l1 s1' ->
sem_instr s2 l2 s2' ->
state_equiv s1' s2' VGamma AGamma /\ l1 = l2.
Proof.
move=> VGamma AGamma [] st1 r1 m1 [] st2 r2 m2 s1' s2' l1 l2 /= hty.
move=> hequiv hstep hstep'. move: (hequiv)=> [] //= hst1 hst2.
move=> hst; subst. move=> {hst1} {hst2}.
move: r1 r2 m1 m2 l1 l2 hstep hstep' hequiv.
elim: hty. 
+ move=> i c hity hcty hc r1 r2 m1 m2 l1 l2 hstep hstep' hequiv.
  induction hity.
  (* x := e *)
  + inversion hstep; (try discriminate).
    inversion hstep'; (try discriminate).
    case:H2=> h1 h2 h3; subst.
    case:H6=> h1' h2' h3'; subst.
    + split; last first. + by auto. 
    apply st_equiv.
    move=> x' hx' /=. move: (hequiv)=> [] //= hr hm heq.
    rewrite /update_rmap /= /update_map /=. 
    case: ifP=> //= hs.
    (* x = x' *)
    + apply eqb_eq in hs. rewrite -hs in hx'.
      rewrite hx' in H. case: H=> ht. rewrite -ht in H1.
      apply sub_public_always_public in H1. 
      move: (expr_equiv_val)=> hexpr. 
      by move: (hexpr VGamma {| scmd_sf := Iassgn x1 e1 :: c1; rmap_sf := r1; mmap_sf := m1 |} 
               {| scmd_sf := Iassgn x1 e1 :: c1; rmap_sf := r2; mmap_sf := m2 |} e1 T' hr H0 H1) => ->.
    (* x != x' *) 
    by move: (hr x' hx')=> ->.
    + move=> a ha /=. move: hequiv=> [] //= hr hm _.
      by move: (hm a ha)=> ->.
  by auto.
  (* x := a[e] *)
  + inversion hstep; (try discriminate).
    inversion hstep'; (try discriminate).
    case:H2=> h1 h2 h3; subst.
    case:H6=> h1' h2' h3'; subst.
    inversion H0;(try discriminate); subst.
    move: (hequiv)=> [] //= hr hm heq.
    move: (expr_equiv_val)=> hexpr. have pub : Public = Public. + by auto.
    move: (hexpr VGamma {| scmd_sf := Iload x1 (AA a1 e0) :: c0; rmap_sf := r1; mmap_sf := m1 |} 
               {| scmd_sf := Iload x1 (AA a1 e0) :: c0; rmap_sf := r2; mmap_sf := m2 |} e0 Public hr H6 pub) => ->.
    split=> /=; last first. + by auto.
    + apply st_equiv. 
      + move=> x' hx' /=. rewrite /update_rmap /update_map /=.
        case: ifP=> //=.
        (* x = x' *) 
        + move=> hs /=. apply eqb_eq in hs; rewrite -hs in hx'.
          rewrite hx' in H. case: H=> ht. rewrite -ht in H1.
          apply sub_public_always_public in H1. rewrite ht in H6. symmetry in ht.
          rewrite H1 in H4. by move: (hm a1 H4)=> ->.
        move=> hneq. by move: (hr x' hx')=> ->.
      + move=> a' ha' /=. 
        by move: (hm a' ha')=> ->.
    by auto.
   (* a[e] := e *)
   + inversion hstep; (try discriminate).
     inversion hstep'; (try discriminate).
     case:H2=> h1 h2 h3; subst.
     case:H6=> h1' h2' h3' h4'; subst.
     inversion H0;(try discriminate); subst; rewrite /=.
     move: (hequiv)=> [] //= hr hm heq.
     move: (expr_equiv_val)=> hexpr. have pub : Public = Public. + by auto.
     move: (hexpr VGamma {| scmd_sf := Istore (AA a1 e1) e'0:: c1; rmap_sf := r1; mmap_sf := m1 |} 
               {| scmd_sf := Istore (AA a1 e1) e'0:: c1; rmap_sf := r2; mmap_sf := m2 |} e1 Public hr H6 pub)=> ->.
     split=> /=; last first. + by auto.
     + apply st_equiv. 
       + move=> x' hx' /=. 
         by move: (hr x' hx') => ->.
       + rewrite /update_mem /= /update_map /=. move=> a ha.
         case: ifP=> //=.
         (* a2 = a *) 
         + move=> hs /=. apply eqb_eq in hs; rewrite -hs in ha. 
           rewrite H4 in ha. case: ha=> hpub. rewrite hpub in H1. apply sub_public_always_public in H1. 
           rewrite H1 in H.
           move: (hexpr VGamma {| scmd_sf := Istore (AA a1 e1) e'0:: c1; rmap_sf := r1; mmap_sf := m1 |} 
               {| scmd_sf := Istore (AA a1 e1) e'0:: c1; rmap_sf := r2; mmap_sf := m2 |} e'0 Public hr H pub)=> ->. 
           rewrite hpub in H4.
           by move: (hm a1 H4)=> ->. 
         move=> hneq. by move: (hm a ha)=> ->.
       by auto.
   (* if b i1 i2 *)
   + inversion hstep; (try discriminate).
     inversion hstep'; (try discriminate).
     case:H2=> h1 h2 h3 h4; subst.
     case:H6=> h1' h2' h3' h4' h5' h6'; subst.
     move: (hequiv)=> [] //= hr hm heq.
     move: (expr_equiv_val)=> hexpr. have pub : Public = Public. + by auto.
     inversion H. apply union_public_always_public in H6. case: H6=>ht1 ht2.
         move: (hexpr VGamma 
         {| scmd_sf := Iif (Ebool bop0 e0 e3) i0 i3 :: c1; rmap_sf := r1; mmap_sf := m1 |}
         {| scmd_sf := Iif (Ebool bop0 e0 e3) i0 i3 :: c1; rmap_sf := r2; mmap_sf := m2 |} e0 T1 hr H4 ht1)=> ->.
         move: (hexpr VGamma 
         {| scmd_sf := Iif (Ebool bop0 e0 e3) i0 i3 :: c1; rmap_sf := r1; mmap_sf := m1 |}
         {| scmd_sf := Iif (Ebool bop0 e0 e3) i0 i3 :: c1; rmap_sf := r2; mmap_sf := m2 |} e3 T2 hr H7 ht2)=> ->.
     split=> /=; last first. + by auto.
     apply st_equiv.
     + move=> x hx /=. by move: (hr x hx)=> ->.
     + move=> a ha /=. by move: (hm a ha)=> ->.
     by auto.
move=> r1 r2 m1 m2 l1 l2 hstep hstep' hequiv; by inversion hstep.
Qed.
     
(* type preserves ct *)
Lemma type_prev_ct : forall VGamma AGamma s1 s2,
type_cmd VGamma AGamma s1.(scmd_sf) ->
constant_time VGamma AGamma s1 s2.
Proof.
move=> VGamma AGamma s1 s2 hty. rewrite /constant_time /=.
move=> s1' s2' l1 l2 n hequiv hmulti hmulti'.
split; last first.
+ by split=> //= hst; apply safe_lang.
move: s1 s2 l1 l2 hmulti hmulti' hequiv hty.
induction n.
+ move=> s1 s2 l1 l2 hmulti hmulti' hequiv hty.
  inversion hmulti; (try discriminate); subst.
  inversion hmulti'; (try discriminate); subst; auto.
  + by case:(n) H.
  by case: (n) H.
move=> s1 s2 l1 l2 hmulti hmulti' hequiv hty. 
inversion hmulti; (try discriminate); subst.
inversion hmulti'; (try discriminate); subst; auto.
move: (type_prev_ct_step)=> hprev. 
move: (hprev VGamma AGamma s1 s2 s' s'0 l l0 hty hequiv H0 H2)=> [hequiv'] heql; subst.
rewrite -H in H1. apply PeanoNat.Nat.add_cancel_r in H1; subst.
rewrite -(addn1 n) in H. apply PeanoNat.Nat.add_cancel_r in H; subst.
move: (preservation hty H0)=> hty'.
by move: (IHn s' s'0 l' l'0 H3 H6 hequiv' hty')=> ->.
Qed.




