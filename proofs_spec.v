Require Import Nat.
Require Import String.
Require Import List.
From mathcomp Require Import all_ssreflect all_algebra.
From LF Require Export lang_spec type_spec.

Set Implicit Arguments.

Inductive state_equiv_spec (s1 s2:state) (VGamma:venv) (AGamma:aenv) : Prop :=
| st_equiv_spec : 
  s1.(scmd) = s2.(scmd) ->
  s1.(ms) = s2.(ms) ->
  (forall x, VGamma x = Some Public -> s1.(rmap) x = s2.(rmap) x) ->
  (not s1.(ms) -> 
     (forall x, VGamma x = Some PublicLoad -> s1.(rmap) x = s2.(rmap) x) /\
     (forall a, AGamma a = Some APublic -> s1.(mmap) a = s2.(mmap) a)) ->
  state_equiv_spec s1 s2 VGamma AGamma.


Definition constant_time (VGamma:venv) (AGamma:aenv) (s1 s2:state) := 
forall s1' s2' d l1 l2 n,
state_equiv_spec s1 s2 VGamma AGamma ->
multi_step_spec s1 d l1 n s1' ->
multi_step_spec s2 d l2 n s2' -> 
l1 = l2 /\ (safe_state s1' <-> safe_state s2').

Lemma progress : forall VGamma AGamma s,
type_cmd VGamma AGamma s.(scmd) ->
safe_state s.
Proof.
move=> VGamma AGamma [] /= []. 
(* empty *)
+ by left.
(* i::c *)
move=> i c r m b hty. induction hty. induction H.
(* x := e:: c*)
+ right.
  exists Dstep.
  exists Lempty. 
  exists {| scmd := c0; 
            rmap := update_rmap r x 
                       (sem_expr_spec {| scmd := Iassgn x e :: c0; rmap := r; mmap := m; ms := b |} e);
            mmap := m;
            ms := b |}.
  by apply Iassgn_sem_spec.
(* x := a[e]::c *) (* array can be public/secret *)
+ case: a H0=> a e H0. right. 
  exists (Dload a (sem_expr_spec {| scmd := Iload x (AA a e) :: c0; rmap := r; mmap := m; ms := b |} e)).
  exists (Lindex (sem_expr_spec {| scmd := Iload x (AA a e) :: c0; rmap := r; mmap := m; ms := b |} e)).
  exists {| scmd := c0; 
            rmap := update_rmap r x 
                       (Array.get (mmap {| scmd := Iload x (AA a e) :: c0; rmap := r; mmap := m; ms := b |} a) 
                       (sem_expr_spec {| scmd := Iload x (AA a e) :: c0; rmap := r; mmap := m; ms := b |} e));
            mmap := m;
            ms := b |}.
  by apply Iload_sem_spec. 
(* a[e] := e *)
+ case: a H0=> a ei H0. right. 
  exists (Dstore a (sem_expr_spec {| scmd := Istore (AA a ei) e :: c0; rmap := r; mmap := m; ms := b |} ei)). 
  exists (Lindex (sem_expr_spec {| scmd := Istore (AA a ei) e :: c0; rmap := r; mmap := m; ms := b |} ei)).
  exists {| scmd := c0; 
            rmap := r;
            mmap := update_mem m a 
                       (sem_expr_spec {| scmd := Istore (AA a ei) e :: c0; rmap := r; mmap := m; ms := b |} ei) 
                       (sem_expr_spec {| scmd := Istore (AA a ei) e :: c0; rmap := r; mmap := m; ms := b |} e);
            ms := b |}.  
  by apply Istore_sem_spec. 
(* if b i1 i2 *)
+ case: b0 H=> b0 e1 e2 H. right.
  exists (Dforce (eval_bool_op b0 
                 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e1) 
                 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e2))).
  exists (Lbool (eval_bool_op b0 
                (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e1) 
                (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e2))).
  exists {| scmd := (if (eval_bool_op b0 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e1) 
                                        (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e2)) 
                        then i0 
                        else i') ++ c0; 
            rmap := {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |}.(rmap);
            mmap := {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |}.(mmap);
            ms := if (eval_bool_op b0 
                     (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e1) 
                     (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e2)) == 
                     (eval_bool_op b0 
                     (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e1) 
                     (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e2)) 
                  then {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |}.(ms) else true |}.
  by apply Iif_sem_spec with b0 e1 e2 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e1) (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e2).
(* protect x v *)
+ right. 
  exists Dstep. 
  exists Lempty. 
  exists {| scmd := c0; 
            rmap := if b then update_rmap r x 0 else update_rmap r x (r y);
            mmap := m;
            ms := b |}.
  by apply Iprotect_sem_spec. 
by left. 
Qed.

Lemma union_public_eq : forall T T',
union_vlevel T T' = Public ->
T = Public /\ T' = Public.
Proof.
unfold union_vlevel. move=> T T'.
case: T=> //=.
by case: T'=> //=.
Qed.

Lemma union_publicload_eq : forall T T',
union_vlevel T T' = PublicLoad ->
T = PublicLoad \/ T = Public.
Proof.
unfold union_vlevel. move=> T T'.
case: T=> //=.
+ case: T'=> //=. move=> h. by right.
case: T' => //=.
+ move=> h; by left.
by left.
Qed.

Lemma public_subtype_publicload : forall T,
sub_vlevel T Public = true ->
sub_vlevel T PublicLoad.
Proof.
move=> T ht. by case: T ht=> //=.
Qed.

Definition public_ms ms := if ms then Public else PublicLoad.

Lemma sub_public_always_public : forall T,
sub_vlevel T Public = true ->
T = Public.
Proof.
by move=> [] //=.
Qed.

Lemma sub_publicload_public_publicload : forall T,
sub_vlevel T PublicLoad = true ->
T = Public. 
Proof.
by move=> [] //= ht. 
Qed.

Lemma sub_sub_vlevel : forall T T',
sub_vlevel (union_vlevel T T') Public ->
sub_vlevel T Public /\ sub_vlevel T' Public.
Proof.
move=> T T' h.
split=> //=;
apply sub_public_always_public in h; rewrite /=.
apply union_public_eq in h; by case: h=> ->.
apply union_public_eq in h; by case: h=> _ ->.
Qed.

Lemma sub_sub_vlevel' : forall T T',
sub_vlevel (union_vlevel T T') PublicLoad ->
sub_vlevel T PublicLoad /\ sub_vlevel T' PublicLoad.
Proof.
move=> T T' h.
split=> //=.
+ case: T h=> //=. by case: T'=> //=. 
case: T' h=> //=.
+ by case: T=> //=.
by case: T.
Qed.

Lemma expr_equiv_val : forall VGamma AGamma s1 s2 e T,
state_equiv_spec s1 s2 VGamma AGamma ->
type_expr VGamma e T ->
sub_vlevel T (public_ms (s1.(ms))) ->
sem_expr_spec s1 e = sem_expr_spec s2 e.
Proof.
move=> VGamma AGamma [] st1 r1 m1 b1 [] st2 r2 m2 b2 e T /= hvar hty hteq.
move: hvar. move=> [] /= hst hb hx hms; subst.
induction hty.
+ rewrite /public_ms in hteq. case: b2 hms hteq.
  + move=> hms hteq. case: T H hteq=> //=.
    move=> hx' _. by move: (hx x hx').
  move=> hms hteq. case: T H hteq=> //=.
  move=> hx' _. by move: (hx x hx').
rewrite /public_ms /= in hteq. case: b2 hms IHhty1 IHhty2 hteq.
+ move=> ht /= h1 h2 /= h. apply sub_sub_vlevel in h.
  case: h=> h1' h2'.
  case: o=> //=;move: (h1 h1') => ->; by move: (h2 h2') => ->.
move=> ht /= h1 h2 /= h. apply sub_sub_vlevel' in h.
case: h=> h1' h2'.
case: o=> //=;move: (h1 h1') => ->; by move: (h2 h2') => ->.
Qed.

Lemma expr_equiv_val_public : forall VGamma s1 s2 e T,
(forall x ,VGamma x = Some Public ->
 s1.(rmap) x = s2.(rmap) x) ->
type_expr VGamma e T ->
T = Public ->
sem_expr_spec s1 e = sem_expr_spec s2 e.
Proof.
move=> VGamma [] st1 r1 m1 b1 [] st2 r2 m2 b2 e T /= hvar hty hteq.
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
move=> [] st r m b /=. case: st=> //=.
+ by left.
move=> i c. case: i.
(* x := e:: c*)
+ move=> x e. right.
  exists Dstep.
  exists Lempty. 
  exists {| scmd := c; 
            rmap := update_rmap r x 
                       (sem_expr_spec {| scmd := Iassgn x e :: c; rmap := r; mmap := m; ms := b |} e);
            mmap := m;
            ms := b |}.
  by apply Iassgn_sem_spec.
(* x := a[e]::c *) (* array can be public/secret *)
+ move=> x a. case: a=> a e. right. 
  exists (Dload a (sem_expr_spec {| scmd := Iload x (AA a e) :: c; rmap := r; mmap := m; ms := b |} e)).
  exists (Lindex (sem_expr_spec {| scmd := Iload x (AA a e) :: c; rmap := r; mmap := m; ms := b |} e)).
  exists {| scmd := c; 
            rmap := update_rmap r x 
                       (Array.get (mmap {| scmd := Iload x (AA a e) :: c; rmap := r; mmap := m; ms := b |} a) 
                       (sem_expr_spec {| scmd := Iload x (AA a e) :: c; rmap := r; mmap := m; ms := b |} e));
            mmap := m;
            ms := b |}.
  by apply Iload_sem_spec. 
(* a[e] := e *)
+ move=> a e. case: a=> a ei. right. 
  exists (Dstore a (sem_expr_spec {| scmd := Istore (AA a ei) e :: c; rmap := r; mmap := m; ms := b |} ei)). 
  exists (Lindex (sem_expr_spec {| scmd := Istore (AA a ei) e :: c; rmap := r; mmap := m; ms := b |} ei)).
  exists {| scmd := c; 
            rmap := r;
            mmap := update_mem m a 
                       (sem_expr_spec {| scmd := Istore (AA a ei) e :: c; rmap := r; mmap := m; ms := b |} ei) 
                       (sem_expr_spec {| scmd := Istore (AA a ei) e :: c; rmap := r; mmap := m; ms := b |} e);
            ms := b |}.  
  by apply Istore_sem_spec. 
(* if b i1 i2 *)
+ move=> b0 i1 i2. case: b0=> b0 e1 e2. right.
  exists (Dforce (eval_bool_op b0 
                 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e1) 
                 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e2))).
  exists (Lbool (eval_bool_op b0 
                (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e1) 
                (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e2))).
  exists {| scmd := (if (eval_bool_op b0 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e1) 
                                        (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e2)) 
                        then i1 
                        else i2) ++ c; 
            rmap := {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |}.(rmap);
            mmap := {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |}.(mmap);
            ms := if (eval_bool_op b0 
                     (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e1) 
                     (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e2)) == 
                     (eval_bool_op b0 
                     (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e1) 
                     (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e2)) 
                  then {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |}.(ms) else true |}.
  by apply Iif_sem_spec with b0 e1 e2 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e1) (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e2).
(* protect x y *)
+ move=> x y. right. 
  exists Dstep. 
  exists Lempty.
  exists {| scmd := c; 
            rmap := if b then update_rmap r x 0 else update_rmap r x (r y);
            mmap := m;
            ms := b |}.
  by apply Iprotect_sem_spec. 
Qed.

Lemma leakage_eq_n : forall s d l n s',
multi_step_spec s d l n s' ->
size l = n.
Proof.
move=> [] st r m b d l n [] st' r' m' b' hmulti.
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

Lemma preservation : forall VGamma AGamma s1 d1 l1 s1',
type_cmd VGamma AGamma s1.(scmd) ->
sem_instr_spec s1 d1 l1 s1' ->
type_cmd VGamma AGamma s1'.(scmd).
Proof.
move=> VGamma AGamma [] st r m b d1 l1 s1' hty hstep.
induction hstep.
(* x := e *)
+ rewrite /update_rmap /update_map /=. rewrite H in hty.
  by inversion hty.
(* if b i1 i2 *)
+ rewrite H /= in hty. inversion hty; subst.
  inversion H5; subst.
  case: ifP=> //=.
  (* true *)
  + move=> htrue. by move: (type_concat H4 H6).
  (* false *)
  move=> hfalse. by move: (type_concat H7 H6).
(* x := a[e] *)
+ rewrite /update_rmap /update_map /=. rewrite H in hty.
  by inversion hty.
(* a[e] := e *)
+ rewrite /update_rmap /update_map /=. rewrite H in hty.
  by inversion hty.
(* protect x v *)
rewrite /update_rmap /update_map /=. rewrite H in hty.
by inversion hty.
Qed.

Lemma step_spec_spec : forall s d l s',
sem_instr_spec s d l s' ->
s.(ms) = true ->
s'.(ms) = true.
Proof.
move=> [] st1 r1 m1 ms d l s' hstep /= hms; subst.
inversion hstep; auto.
rewrite /= in H6. rewrite /=.
by case: ifP=> //=.
Qed.

Lemma step_deterministic_dir : forall s d l1 s1 l2 s2,
sem_instr_spec s d l1 s1 ->
sem_instr_spec s d l2 s2 ->
l1 = l2 /\ s1 = s2.
Proof.
move=> [] st1 r1 m1 ms1 d l1 s2 l2 s2' hstep hstep'.
inversion hstep; (try discriminate); subst.
(* x := e *)
+ inversion hstep'; (try discriminate); subst.
  rewrite /= in H H0 hstep hstep'; subst.
  split=> //=. by case: H0=> h1 h2 h3; subst.
  rewrite H in H0. by inversion H0.
(* if b i i' *)
+ inversion hstep'; (try discriminate); subst.
  rewrite /= in H H1 hstep hstep'; subst.
  case: H1=> h1 h2 h3 h4 h5 h6; subst. by split=> //=.
(* x := a[e] *)
+ inversion hstep'; (try discriminate); subst.
  rewrite /= in H H3 H5 hstep hstep'; subst.
  case: H5=> h1 h2 h3; subst. by split=> //=.
(* a[e] := e *)
+ inversion hstep'; (try discriminate); subst.
  rewrite /= in H H3 H5 hstep hstep'; subst.
  case: H5=> h1 h2 h3; subst. by split=> //=.
(* protect *)
inversion hstep'; (try discriminate); subst.
+ rewrite /= in H H0 hstep hstep'; subst.
  case: H0=> h1 h2; subst. by split=> //=.
rewrite /= in H H0 hstep hstep'; subst.
case: H0=> h1 h2 h3; subst. by split=> //=.
Qed.

Lemma type_prev_ct_step : forall VGamma AGamma s1 s2 s1' s2' d l1 l2,
type_cmd VGamma AGamma s1.(scmd) ->
state_equiv_spec s1 s2 VGamma AGamma ->
sem_instr_spec s1 d l1 s1' ->
sem_instr_spec s2 d l2 s2' ->
state_equiv_spec s1' s2' VGamma AGamma /\ l1 = l2. 
Proof.
move=> VGamma AGamma [] st1 r1 m1 b1 [] st2 r2 m2 b2 s1' s2' d l1 l2 /= hty.
move=> hequiv hstep hstep'. move: (hequiv)=> [] //= hst hms hr hm; subst.
move=> {hr} {hm}.
move: r1 r2 m1 m2 d l1 l2 hstep hstep' hequiv.
elim: hty. 
+ move=> i c hity hcty hc r1 r2 m1 m2 d l1 l2 hstep hstep' hequiv.
  induction hity.
  (* x := e *)
  + inversion hstep; (try discriminate).
    inversion hstep'; (try discriminate).
    case:H2=> h1 h2 h3; subst.
    case:H7=> h1' h2' h3'; subst.
    + split; last first. + by auto.
    move: (expr_equiv_val)=> hexpr.
        move: (hexpr VGamma AGamma {| scmd := Iassgn x1 e1 :: c1; rmap := r1; mmap := m1; ms := b2 |} 
               {| scmd := Iassgn x1 e1 :: c1; rmap := r2; mmap := m2; ms := b2 |} e1 T' hequiv H0)=> he.  
    apply st_equiv_spec; rewrite /=.
    (* instr equal *)
    + by auto.
    (* ms equal *)
    + by auto.
    (* equal on public type *)
    + move=> x' hx' /=. move: (hequiv)=> [] //= hr hm heq.
      rewrite /update_rmap /= /update_map /=. move=> h'.
      case: ifP=> //= hs.
      (* x = x' *)
      + apply eqb_eq in hs. rewrite -hs in hx'.
        rewrite hx' in H. case: H=> ht. rewrite -ht in H1. 
        rewrite /public_ms /= in he. move: he. case: ifP=> //=.
        + move=> hb2 /= he. by move: (he H1)=> ->. 
        move=> hb2 /= he. apply public_subtype_publicload in H1.
        by move: (he H1)=> ->. 
      (* x != x' *) 
      by move: (heq x' hx')=> ->.
    (* no misspeculation case *)
    move: (hequiv)=> [] //= hr hm heq.
    rewrite /update_rmap /= /update_map /=. move=> h'.
    move=> hb. split=> //=.
    move=> x hx. case: ifP=> //= hs.
    + apply eqb_eq in hs; subst. 
      rewrite /public_ms /= in he. move: he. case: ifP=> //=.
      + move=> hb2 /= he. rewrite H in hx. case: hx=> ht; subst. 
        apply sub_publicload_public_publicload in H1.
        case: H1=> H1'; subst. 
        + have H1 : sub_vlevel Public PublicLoad. + by auto.
          by move: (he H1)=> ->.
        move: (h' hb)=> [] hr' hm'. 
        by move: (hr' x hx).
      by move: (h' hb)=> [] hpub ha. 
  (* x := a[e] *)
  + inversion hstep; (try discriminate).
    inversion hstep'; (try discriminate).
    case:H2=> h1 h2 h3; subst.
    case:H7=> h1' h2' h3' h4'; subst.
    inversion H0;(try discriminate); subst.
    move: (hequiv)=> [] //= hr _ heq hm.
    move: (expr_equiv_val)=> hexpr. have pub : Public = Public. + by auto.
    move: (hexpr VGamma AGamma {| scmd := Iload x1 (AA a1 e0) :: c1; rmap := r1; mmap := m1; ms := b2 |} 
               {| scmd := Iload x1 (AA a1 e0) :: c1; rmap := r2; mmap := m2; ms := b2 |} e0 Public hequiv H6)=> /= he.
    have htrue : true. auto. move: (he htrue)=> {he} he.
    split=> /=; last first. + by auto.
    apply st_equiv_spec; rewrite /=.
    (* instr equal *)
    + by auto.
    (* ms equal *)
    + by auto.
    (* equal on public type *)
    + move=> x' hx' /=. rewrite /update_rmap /update_map /=.
      case: ifP=> //=.
      (* x = x' *) 
      + move=> hs /=. apply eqb_eq in hs; rewrite -hs in hx'.
        rewrite hx' in H. case: H=> ht. rewrite -ht in H1.
        apply sub_public_always_public in H1. rewrite ht in H6. symmetry in ht.
        by case: (T') H1=> //=.
      move=> hneq. by move: (heq x' hx')=> ->.
    (* no misspeculation case *)
    rewrite /update_rmap /= /update_map /=. move=> h'.
    split=> //=.
    move=> x hx. case: ifP=> //= hs.
    + apply eqb_eq in hs; subst. 
      rewrite /public_ms /= in he. move: he=> ->. 
      move: (hm h')=> [] h1 h2. rewrite H in hx. case: hx=> hxx; subst.
      case: T' H1 H0 H4=> //= ht /= H0 H4.
      move: (hm h')=> [] hr' hm'. 
      by move: (hr' x hx).
    by move: (hm h')=> [] h1 h2. 
   (* a[e] := e *)
   + inversion hstep; (try discriminate).
     inversion hstep'; (try discriminate).
     case:H2=> h1 h2 h3; subst.
     case:H7=> h1' h2' h3' h4'; subst.
     inversion H0;(try discriminate); subst; rewrite /=.
     move: (hequiv)=> [] //= hr hm heq.
     move: (expr_equiv_val)=> hexpr. have pub : Public = Public. + by auto.
     move: (hexpr VGamma AGamma {| scmd := Istore (AA a1 e1) e'0:: c1; rmap := r1; mmap := m1; ms := b2 |} 
               {| scmd := Istore (AA a1 e1) e'0:: c1; rmap := r2; mmap := m2; ms := b2 |} e1 Public hequiv H6) => /= he.
     have htrue : true. auto. move: (he htrue)=> {he} he. 
     split=> /=; last first. + by auto.
     apply st_equiv_spec. 
     (* instr equal *)
     + by auto. 
     (* ms equal *)
     + by auto. 
     (* equal on public type *)
     + move=> x' hx' /=.
       by move: (heq x' hx') => ->.
     (* no misspeculation case *)
     rewrite /=.
     rewrite /update_mem /= /update_map /=. split=> //=.
     + move: (a H2)=> [] h1 h2. by apply h1.
     move=> a' ha'.
     case: ifP=> //=.
     + move=> hs /=. apply eqb_eq in hs; rewrite -hs in ha'. 
       rewrite H4 in ha'. case: ha'=> hpub. rewrite hpub in H4.
       rewrite hpub /alevel_to_vlevel in H1. rewrite he /=.
       apply sub_publicload_public_publicload in H1.
       case: H1.
       (* right hand side is Public *)
       + move=> H1'; subst. have H1 : sub_vlevel Public PublicLoad. + by auto.
         move: (hexpr VGamma AGamma {| scmd := Istore (AA a' e1) e'0:: c1; rmap := r1; mmap := m1; ms := b2 |} 
               {| scmd := Istore (AA a' e1) e'0:: c1; rmap := r2; mmap := m2; ms := b2 |} e'0 Public hequiv H)=> /= he'.
         move: (he' htrue)=> ->. move: (a H2)=> [] h1 h2. by move: (h2 a' H4)=> ->.
       move=> H1'; subst. move: (a H2)=> [] hr' hm'. by move: (hm' a' ha').
   (* if b i1 i2 *)
   + inversion hstep; (try discriminate).
     inversion hstep'; (try discriminate).
     case:H2=> h1 h2 h3 h4; subst.
     case:H10=> h1' h2' h3' h4' h5' h6'; subst.
     case: H15=> h7; subst.
     move: (hequiv)=> [] //= hr hm heq.
     move: (expr_equiv_val)=> hexpr. have pub : Public = Public. + by auto.
     inversion H. apply union_public_eq in H6. case: H6=>ht1 ht2.
     move: (hexpr VGamma AGamma 
         {| scmd := Iif (Ebool bop0 e0 e3) i0 i3 :: c1; rmap := r1; mmap := m1; ms := b2 |}
         {| scmd := Iif (Ebool bop0 e0 e3) i0 i3 :: c1; rmap := r2; mmap := m2; ms := b2 |} e0 T1 hequiv H4)=> /= he1. 
     move: (hexpr VGamma AGamma 
         {| scmd := Iif (Ebool bop0 e0 e3) i0 i3 :: c1; rmap := r1; mmap := m1; ms := b2 |}
         {| scmd := Iif (Ebool bop0 e0 e3) i0 i3 :: c1; rmap := r2; mmap := m2; ms := b2 |} e3 T2 hequiv H7)=> /= he2.
     move=> hb2. rewrite /public_ms /= in he1 he2. 
     case: b2 hc hstep' hequiv hstep hm hb2 he1 he2=> //=.
     + subst. move=> hc hstep' hequiv hstep hm hb2 /= he1 /= he2.
       have htrue : true. auto. move: (he1 htrue)=> {he1} ->. move: (he2 htrue)=> {he2} ->.
       split=> //=. 
       apply st_equiv_spec.
       (* instr equal *)
       + by auto.
       (* ms equal *)
       + by auto. 
       move=> x hx /=. by move: (heq x hx)=> ->.
    rewrite /=. case: ifP=> //=.
    move=> /= b hb hx a ha; subst. move=> ha' /= he1' /= he2' /=. have htrue : true. auto.
    move: (he1' htrue)=> {he1'} ->. move: (he2' htrue)=> {he2'} ->. split=> //=.
    apply st_equiv_spec.
    (* instr equal *)
    + by auto.
    (* ms equal *)
    + by auto. 
    + move=> x hx' /=. by move: (heq x hx')=> ->.
    move=> /= b2. split=> //=.
    + move=> x hx'. move: (ha' not_false_is_true)=> [] h1 h2. by apply h1.
    move: (ha' not_false_is_true)=> [] h1 h2. by apply h2.
   (* protect *)
   + inversion hstep; (try discriminate); subst.
     inversion hstep'; (try discriminate); subst.
     case:H2=> h1 h2; subst.
     case:H3=> h1' h2' h3' h4'; subst.
     move: (hequiv)=> [] //= hr hm heq.
     split=> /=; last first. + by auto.
     apply st_equiv_spec.
     (* instr equal *)
     + by auto.
     (* ms equal *)
     + by auto.
     (* equal on public type *)
     + move=> x' hx' /=. case: ifP=> //=.
       (* misspeculation is set *)
       + move=> hb. rewrite /update_rmap /update_map /=. 
         case: ifP=> //=. move=> hx. by move: (heq x' hx')=> ->.
       (* misspeculation not set *)
       move=> hb. rewrite /update_rmap /update_map /=. 
       case: ifP=> //=.
       + move=> hs. apply eqb_eq in hs; subst.
         case: T H0 H1=> //=.
         + move=> hy _. by move: (heq y1 hy).
       move=> hs. by move: (heq x' hx'). 
    (* no misspeculation case *)
    move=> /= b. split=> //=. case: b2 hstep' hc hstep hequiv heq hm a b=> //= hstep' hc hstep hequiv heq hm a b.
    move=> x hx. rewrite /update_rmap /update_map /=.
    case: ifP=> //=.
    + move=> hs. apply eqb_eq in hs; subst.
      case: (T) H0 H1=> //= hy1 _. + by move: (heq y1 hy1).
      move: (a b)=> [] hr' hm'; subst.  move: (a b)=> [] hr'' hm''. by move: (hr'' x hx).
    move: (a b)=> [] h1 h2. by apply h2. 
move=> r1 r2 m1 m2 d l1 l2 hstep hstep' hequiv; by inversion hstep.
Qed.

(* type preserves ct *)
Lemma type_prev_ct : forall VGamma AGamma s1 s2,
type_cmd VGamma AGamma s1.(scmd) ->
constant_time VGamma AGamma s1 s2.
Proof.
move=> VGamma AGamma s1 s2 hty. rewrite /constant_time /=.
move=> s1' s2' d l1 l2 n hequiv hmulti hmulti'.
split; last first.
+ by split=> //= hst; apply safe_lang.
move: s1 s2 d l1 l2 hmulti hmulti' hequiv hty.
induction n.
+ move=> s1 s2 d l1 l2 hmulti hmulti' hequiv hty.
  inversion hmulti; (try discriminate); subst.
  inversion hmulti'; (try discriminate); subst; auto.
  by case:(n) H.
move=> s1 s2 d l1 l2 hmulti hmulti' hequiv hty. 
inversion hmulti; (try discriminate); subst.
inversion hmulti'; (try discriminate); subst; auto.
move: (type_prev_ct_step)=> hprev. 
move: (hprev VGamma AGamma s1 s2 s' s'0 d0 l l0 hty hequiv H0 H7)=> [hequiv'] heql; subst.
rewrite -H in H5. apply PeanoNat.Nat.add_cancel_r in H5; subst.
rewrite -(addn1 n) in H. apply PeanoNat.Nat.add_cancel_r in H; subst.
move: (preservation hty H0)=> hty'.
by move: (IHn s' s'0 d' l' l'0 H4 H9 hequiv' hty')=> ->.
Qed.

