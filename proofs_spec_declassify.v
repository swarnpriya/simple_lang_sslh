Require Import Nat.
Require Import String.
Require Import List.
From mathcomp Require Import all_ssreflect all_algebra.
From LF Require Export lang_spec_declassify type_spec_declassify.

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


Definition constant_time_spec (VGamma:venv) (AGamma:aenv) (s1 s2:state) := 
forall s1' s2' d l1 l2 n,
state_equiv_spec s1 s2 VGamma AGamma ->
multi_step_spec s1 d l1 n s1' ->
multi_step_spec s2 d l2 n s2' -> 
l1 = l2 /\ (safe_state s1' <-> safe_state s2').

Definition extract_declassify_leakage_spec (l : leakage) : option value :=
match l with 
 | Ldeclassify v => v
 | _ => None
end. 

Fixpoint extract_declassify_leakages_spec (l : seq leakage) : seq (option value) :=
match l with 
 | [::] => [::]
 | l :: ls => extract_declassify_leakage_spec l :: extract_declassify_leakages_spec ls
end.

Fixpoint extract_declassify_leakagess_spec (l : seq (seq leakage)) : seq (seq (option value)) :=
match l with 
 | [::] => [::]
 | l :: ls => extract_declassify_leakages_spec l :: extract_declassify_leakagess_spec ls
end.

Definition constant_time_declassify_spec (VGamma:venv) (AGamma:aenv) (s1 s2:state) := 
forall s1' s2' d l1 l2 n,
state_equiv_spec s1 s2 VGamma AGamma ->
multi_step_spec s1 d l1 n s1' ->
multi_step_spec s2 d l2 n s2' ->
extract_declassify_leakagess_spec l1 = extract_declassify_leakagess_spec l2 /\
(safe_state s1' <-> safe_state s2').

Lemma progress : forall VGamma AGamma s,
type_cmd VGamma AGamma s.(scmd) ->
safe_state s.
Proof.
move=> VGamma AGamma [] /= []. 
(* empty *)
+ by left.
(* i::c *)
move=> i c r m b hty. induction hty. induction H.
(* Iempty :: c *)
+ right. 
  exists Dstep.
  exists [::].
  exists {| scmd := c0; 
            rmap := r;
            mmap := m;
            ms := b |}.
  by apply Iempty_sem_spec.
(* x := e:: c*)
+ right.
  exists Dstep. 
  exists (if d 
          then [:: Ldeclassify (Some (sem_expr_spec {| scmd := Iassgn x d e :: c0; rmap := r; mmap := m; ms := b |} e))] 
          else [:: Lempty]). 
  exists {| scmd := c0; 
            rmap := update_rmap r x 
                       (sem_expr_spec {| scmd := Iassgn x d e :: c0; rmap := r; mmap := m; ms := b |} e);
            mmap := m;
            ms := b |}.
  by apply Iassgn_sem_spec.
(* x := a[e]::c *) (* array can be public/secret *) 
+ case: a H0=> a e H0. right. 
  exists (Dload a (sem_expr_spec {| scmd := Iload x d (AA a e) :: c0; rmap := r; mmap := m; ms := b |} e)).
  exists  (if d 
           then [:: Lindex (sem_expr_spec {| scmd := Iload x d (AA a e) :: c0; rmap := r; mmap := m; ms := b |} e);
                    Ldeclassify 
                    (Some (Array.get (mmap {| scmd := Iload x d (AA a e) :: c0; rmap := r; mmap := m; ms := b |} a) 
                           (sem_expr_spec {| scmd := Iload x d (AA a e) :: c0; rmap := r; mmap := m; ms := b |} e)))]
                else [:: Lindex (sem_expr_spec {| scmd := Iload x d (AA a e) :: c0; rmap := r; mmap := m; ms := b |} e)]).
  exists {| scmd := c0; 
            rmap := update_rmap r x 
                       (Array.get (mmap {| scmd := Iload x d (AA a e) :: c0; rmap := r; mmap := m; ms := b |} a) 
                       (sem_expr_spec {| scmd := Iload x d (AA a e) :: c0; rmap := r; mmap := m; ms := b |} e));
            mmap := m;
            ms := b |}.
  by apply Iload_sem_spec. 
(* a[e] := e *)
+ case: a H0=> a ei H0. right. 
  exists (Dstore a (sem_expr_spec {| scmd := Istore (AA a ei) d e :: c0; rmap := r; mmap := m; ms := b |} ei)). 
  exists (if d 
          then [:: Lindex (sem_expr_spec {| scmd := Istore (AA a ei) d e :: c0; rmap := r; mmap := m; ms := b |} ei);
                   Ldeclassify (Some (sem_expr_spec {| scmd := Istore (AA a ei) d e :: c0; rmap := r; mmap := m; ms := b |} e))]
          else [:: Lindex (sem_expr_spec {| scmd := Istore (AA a ei) d  e :: c0; rmap := r; mmap := m; ms := b |} ei)]).
  exists {| scmd := c0; 
            rmap := r;
            mmap := update_mem m a 
                       (sem_expr_spec {| scmd := Istore (AA a ei) d e :: c0; rmap := r; mmap := m; ms := b |} ei) 
                       (sem_expr_spec {| scmd := Istore (AA a ei) d e :: c0; rmap := r; mmap := m; ms := b |} e);
            ms := b |}.  
  by apply Istore_sem_spec. 
(* if b i1 i2 *)
+ case: b0 H=> b0 e1 e2 H. right.
  exists (Dforce (eval_bool_op b0 
                 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e1) 
                 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e2))).
  exists [::(Lbool (eval_bool_op b0 
                (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e1) 
                (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i0 i' :: c0; rmap := r; mmap := m; ms := b |} e2)))].
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
  exists [::Lempty]. 
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

Lemma sub_publicload_public : forall T,
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
(* Iempty *)
+ right. exists Dstep. exists [::]. exists {| scmd := c; rmap := r; mmap := m; ms := b |}.
  by apply Iempty_sem_spec.
(* x := e:: c*)
+ move=> x d e. right.
  exists Dstep.
  exists  (if d 
          then [:: Ldeclassify (Some (sem_expr_spec {| scmd := Iassgn x d e :: c; rmap := r; mmap := m; ms := b |} e))] 
          else [:: Lempty]). 
  exists {| scmd := c; 
            rmap := update_rmap r x 
                       (sem_expr_spec {| scmd := Iassgn x d e :: c; rmap := r; mmap := m; ms := b |} e);
            mmap := m;
            ms := b |}.
  by apply Iassgn_sem_spec.
(* x := a[e]::c *) (* array can be public/secret *)
+ move=> x d a. case: a=> a e. right. 
  exists (Dload a (sem_expr_spec {| scmd := Iload x d (AA a e) :: c; rmap := r; mmap := m; ms := b |} e)). 
  exists  (if d 
           then [:: Lindex (sem_expr_spec {| scmd := Iload x d (AA a e) :: c; rmap := r; mmap := m; ms := b |} e);
                    Ldeclassify 
                    (Some (Array.get (mmap {| scmd := Iload x d (AA a e) :: c; rmap := r; mmap := m; ms := b |} a) 
                           (sem_expr_spec {| scmd := Iload x d (AA a e) :: c; rmap := r; mmap := m; ms := b |} e)))]
                else [:: Lindex (sem_expr_spec {| scmd := Iload x d (AA a e) :: c; rmap := r; mmap := m; ms := b |} e)]).
  exists {| scmd := c; 
            rmap := update_rmap r x 
                       (Array.get (mmap {| scmd := Iload x d (AA a e) :: c; rmap := r; mmap := m; ms := b |} a) 
                       (sem_expr_spec {| scmd := Iload x d (AA a e) :: c; rmap := r; mmap := m; ms := b |} e));
            mmap := m;
            ms := b |}.
  by apply Iload_sem_spec. 

(* a[e] := e *)
+ move=> a d e. case: a=> a ei. right. 
  exists (Dstore a (sem_expr_spec {| scmd := Istore (AA a ei) d e :: c; rmap := r; mmap := m; ms := b |} ei)).
  exists (if d 
          then [:: Lindex (sem_expr_spec {| scmd := Istore (AA a ei) d e :: c; rmap := r; mmap := m; ms := b |} ei);
                   Ldeclassify (Some (sem_expr_spec {| scmd := Istore (AA a ei) d e :: c; rmap := r; mmap := m; ms := b |} e))]
          else [:: Lindex (sem_expr_spec {| scmd := Istore (AA a ei) d  e :: c; rmap := r; mmap := m; ms := b |} ei)]).
  exists {| scmd := c; 
            rmap := r;
            mmap := update_mem m a 
                       (sem_expr_spec {| scmd := Istore (AA a ei) d e :: c; rmap := r; mmap := m; ms := b |} ei) 
                       (sem_expr_spec {| scmd := Istore (AA a ei) d e :: c; rmap := r; mmap := m; ms := b |} e);
            ms := b |}.  
  by apply Istore_sem_spec. 
(* if b i1 i2 *)
+ move=> b0 i1 i2. case: b0=> b0 e1 e2. right.
  exists (Dforce (eval_bool_op b0 
                 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e1) 
                 (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e2))).
  exists [::(Lbool (eval_bool_op b0 
                (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e1) 
                (sem_expr_spec {| scmd := Iif (Ebool b0 e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := b |} e2)))].
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
  exists [::Lempty].
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
(* Iempty *)
+ rewrite H /= in hty. by inversion hty; (try discriminate); subst.
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
(* Iempty *)
+ rewrite /= in H. rewrite H /= in hstep'. 
  inversion hstep'; (try discriminate); subst.
  rewrite /= in H0 hstep hstep'; subst.
  split=> //=; by inversion H0.
(* x := e *)
+ rewrite /= in H. rewrite H /= in hstep'. 
  inversion hstep'; (try discriminate); subst.
  rewrite /= in H0 hstep hstep'; subst.
  split=> //=. by case: H0=> /= h1 h2 h3 h4; subst.
  by inversion H0.
(* if b i i' *)
+ inversion hstep'; (try discriminate); subst.
  rewrite /= in H H1 hstep hstep'; subst.
  case: H1=> h1 h2 h3 h4 h5 h6; subst. by split=> //=.
(* x := a[e] *)
+ rewrite /= in H. rewrite H /= in hstep'.
  inversion hstep'; (try discriminate); subst.
  rewrite /= in H3 H5 hstep hstep'; subst.
  case: H5=> h1 h2 h3 h4; subst. by split=> //=.
(* a[e] := e *)
+ rewrite /= in H. rewrite H /= in hstep'.
  inversion hstep'; (try discriminate); subst.
  rewrite /= in H3 H5 hstep hstep'; subst.
  case: H5=> h1 h2 h3 h4; subst. by split=> //=.
(* protect *)
rewrite /= in H. rewrite H /= in hstep'. 
inversion hstep'; (try discriminate); subst.
split=> //=. by case: H0=> h1 h2 h3; subst.
Qed.

Definition declassify_val_spec (d:bool) ve (v : seq (option value)) : value := 
  if d then (odflt 0 (last None v))
  else ve.

Definition build_i_leakage_spec (s: state) (v : seq (option value)) : seq leakage :=
match (nth Iempty (scmd s) 0) with 
 | Iempty => [::]
 | Iassgn x d e => if d then [:: Ldeclassify (nth None v 0)] else [:: Lempty]
 | Iload x d (AA a e) => if d then [:: Lindex (sem_expr_spec s e); Ldeclassify (nth None v 1)]
                              else [:: Lindex (sem_expr_spec s e)]
 | Istore (AA a e) d e' => if d then [:: Lindex (sem_expr_spec s e); Ldeclassify (nth None v 1)] 
                                else [:: Lindex (sem_expr_spec s e)] 
 | Iif (Ebool bop e1 e2) i1 i2 => [:: Lbool (eval_bool_op bop (sem_expr_spec s e1) (sem_expr_spec s e2))]
 | Iprotect x y => [:: Lempty]  
end. 

Inductive build_state_instr_spec : state -> seq (option value) -> directive -> state -> Prop :=
| build_next_empty : forall c r m ms,
                      build_state_instr_spec {| scmd := Iempty :: c; rmap := r; mmap := m; ms := ms |} [::] Dstep
                      {| scmd := c; rmap := r; mmap := m; ms := ms |}
| build_next_assgn : forall x d e c r m ms vs,
                      build_state_instr_spec {| scmd := Iassgn x d e :: c; rmap := r; mmap := m; ms := ms |} vs Dstep
                      {| scmd := c; 
                         rmap := update_rmap r x 
                                  (declassify_val_spec d 
                                   (sem_expr_spec {| scmd := Iassgn x d e :: c; rmap := r; mmap := m; ms := ms |} e) vs);
                         mmap := m; ms := ms |}
| build_next_load : forall x d a e c r m ms vs,
                    build_state_instr_spec {| scmd := Iload x d (AA a e) :: c; rmap := r; mmap := m; ms := ms |} vs 
                    (Dload a (sem_expr_spec {| scmd := Iload x d (AA a e) :: c; rmap := r; mmap := m; ms := ms |} e))
                    {| scmd := c; 
                       rmap := update_rmap r x 
                               (declassify_val_spec d (Array.get (m a) 
                               (sem_expr_spec {| scmd := Iload x d (AA a e) :: c; rmap := r; mmap := m; ms := ms |} e)) vs);
                       mmap := m; 
                       ms := ms |}
| build_next_store : forall d a e e' c r m ms vs,
                     build_state_instr_spec {| scmd := Istore (AA a e) d e' :: c; rmap := r; mmap := m; ms := ms |} vs
                     (Dstore a (sem_expr_spec {| scmd := Istore (AA a e) d e' :: c; rmap := r; mmap := m; ms := ms |} e))
                      {| scmd := c; 
                         rmap := r;
                         mmap := update_mem m a 
                                 (sem_expr_spec {| scmd := Istore (AA a e) d e' :: c; rmap := r; mmap := m; ms := ms |}  e) 
                                 (declassify_val_spec d 
                                 (sem_expr_spec {| scmd := Istore (AA a e) d e' :: c; rmap := r; mmap := m; ms := ms |} e') vs);
                         ms := ms |}
| build_next_if : forall e1 e2 i1 i2 bop bf c r m ms vs,
                  build_state_instr_spec {| scmd := Iif (Ebool bop e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := ms |} vs
                  (Dforce bf)
                  {| scmd := (if bf then i1 else i2) ++ c; 
                     rmap := r;
                     mmap := m;
                     ms := if (eval_bool_op bop 
                               (sem_expr_spec {| scmd := Iif (Ebool bop e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := ms |} e1)
                               (sem_expr_spec {| scmd := Iif (Ebool bop e1 e2) i1 i2 :: c; rmap := r; mmap := m; ms := ms |} e2)) == bf 
                           then ms 
                           else true |}
| build_next_protect : forall x y c r m ms vs,
                       build_state_instr_spec {| scmd := Iprotect x y :: c; rmap := r; mmap := m; ms := ms |} vs
                       Dstep
                       {| scmd := c; 
                          rmap := if ms
                                  then update_rmap r x 0
                                  else update_rmap r x (r y);
                          mmap := m;
                          ms := ms |}.

(*Inductive build_c_leakage_spec : state -> seq (seq (option value)) -> seq (seq leakage) -> Prop :=
| build_leakage_empty_c_vs : forall r m ms, 
                             build_c_leakage_spec {| scmd := [::]; rmap := r; mmap := m; ms := ms |} [::] [::] 
| build_leakage_seq_c_vs   : forall i c r m ms d v vs s' ls,
                             build_state_instr_spec {| scmd := i :: c; rmap := r; mmap := m; ms := ms |} v d s' ->
                             build_c_leakage_spec s' vs ls ->
                             build_c_leakage_spec {| scmd := i :: c; rmap := r; mmap := m; ms := ms |} (v :: vs) 
                             ((build_i_leakage_spec {| scmd := i :: c; rmap := r; mmap := m; ms := ms |}  v) :: ls)
| build_leakage_empty_c_seq_vs : forall r m ms vs, 
                                 build_c_leakage_spec {| scmd := [::]; rmap := r; mmap := m; ms := ms |} vs [::]
| build_leakage_seq_c_empty_vs : forall i c r m ms, 
                                 build_c_leakage_spec {| scmd := i :: c; rmap := r; mmap := m; ms := ms |} [::] [::].*)

Inductive build_c_leakage_spec : state -> seq (seq (option value)) -> seq directive -> seq (seq leakage) -> Prop :=
| build_leakage_empty_c_vs : forall r m ms, 
                             build_c_leakage_spec {| scmd := [::]; rmap := r; mmap := m; ms := ms |} [::] [::] [::] 
| build_leakage_seq_c_vs   : forall i c r m ms d ds v vs s' l ls,
                             build_i_leakage_spec {| scmd := i :: c; rmap := r; mmap := m; ms := ms |}  v = l ->
                             build_state_instr_spec {| scmd := i :: c; rmap := r; mmap := m; ms := ms |} v d s' ->
                             build_c_leakage_spec s' vs ds ls ->
                             build_c_leakage_spec {| scmd := i :: c; rmap := r; mmap := m; ms := ms |} (v :: vs) (d :: ds)
                             (l :: ls)
| build_leakage_empty_c_seq_vs : forall r m ms vs, 
                                 build_c_leakage_spec {| scmd := [::]; rmap := r; mmap := m; ms := ms |} vs [::] [::]
| build_leakage_seq_c_empty_vs : forall i c r m ms, 
                                 build_c_leakage_spec {| scmd := i :: c; rmap := r; mmap := m; ms := ms |} [::] [::] [::].

Lemma declassify_mem_to_leakage_spec : forall VGamma AGamma c,
type_cmd VGamma AGamma c ->
(forall s1 s2 ov, 
   c = s1.(scmd) ->
   state_equiv_spec s1 s2 VGamma AGamma ->
   build_i_leakage_spec s1 ov = build_i_leakage_spec s2 ov).
Proof.
move=> VGamma AGamma c hty.
move=> [] c1 r1 m1 ms1 [] c2 r2 m2 ms2 ov /= hc /= hequiv /=; subst.
move: hequiv=> [] /= hc hms hr hm; subst. rewrite /= in hty.
elim: hty; last first. + by auto.
move=> i c htyi htyc hrec. move: r1 m1 r2 m2 hr hm hrec.
induction htyi.
(* empty *)
+ by move=> r1 m1 r2 m2 hr hm hrec /=.
(* x := e *)
+ by move=> r1 m1 r2 m2 hr hm hrec /=.
(* x := a[e] *)
+ move=> r1 m1 r2 m2 hr hm hrec /=. case: a H0=> //=.
  move=> x' e htya. inversion htya; subst.
  have hpub : Public = Public. + by auto.
  rewrite /build_i_leakage_spec /=.
  have hequiv : state_equiv_spec {| scmd := Iload x d (AA x' e) :: c; rmap := r1; mmap := m1; ms := ms2 |} 
                {| scmd := Iload x d (AA x' e) :: c; rmap := r2; mmap := m2; ms := ms2 |} VGamma AGamma.
  + by auto.
  have hms : sub_vlevel Public (public_ms (ms
              {| scmd := Iload x d (AA x' e) :: c; rmap := r1; mmap := m1; ms := ms2 |})).
  + by auto. 
  by have -> := expr_equiv_val hequiv H5 hms. 
(* a[e] := e *)
+ move=> r1 m1 r2 m2 hrec hm hr. case: a H0=> //=.
  move=> x' ei htya. inversion htya; subst.
  have hpub : Public = Public. + by auto.
  rewrite /build_i_leakage_spec /=.
  have hequiv : state_equiv_spec {| scmd := Istore (AA x' ei) d e :: c; rmap := r1; mmap := m1; ms := ms2 |} 
                {| scmd := Istore (AA x' ei) d e :: c; rmap := r2; mmap := m2; ms := ms2 |} VGamma AGamma.
  + by auto.
  have hms : sub_vlevel Public (public_ms (ms
              {| scmd := Istore (AA x' ei) d e :: c; rmap := r1; mmap := m1; ms := ms2 |})).
  + by auto.
  by have -> := expr_equiv_val hequiv H5 hms. 
(* if e i i' *)
+ move=> r1 m1 r2 m2 hr hm hrec /=. case: b H=> //= b' e e' hty.
  inversion hty; subst. apply union_public_eq in H5.
  case H5=> h5 h6; subst. case: H5=> hpub _.
  rewrite /build_i_leakage_spec /=.
  have hequiv : state_equiv_spec {| scmd := Iif (Ebool b' e e') i i' :: c; rmap := r1; mmap := m1; ms := ms2 |} 
                {| scmd := Iif (Ebool b' e e') i i' :: c; rmap := r2; mmap := m2; ms := ms2 |} VGamma AGamma.
  + by auto.
  have hms : sub_vlevel Public (public_ms (ms
              {| scmd := Iif (Ebool b' e e') i i' :: c; rmap := r1; mmap := m1; ms := ms2 |})).
  + by auto.
  have -> := expr_equiv_val hequiv H3 hms. by have -> := expr_equiv_val hequiv H6 hms.
(* protect *)
move=> r1 m1 r2 m2 hr hm hrec /=.
by rewrite /build_i_leakage_spec /=.
Qed.

Lemma declassify_to_leakage_i_spec :
forall s1 s1' d l c, 
 c = s1.(scmd) -> 
 sem_instr_spec s1 d l s1' -> 
 build_i_leakage_spec s1 (extract_declassify_leakages_spec l) = l.
Proof.
move=> s1 s1' d l c. case: s1=> c1 r1 m1 ms /= hc; subst.
case: c1=> //=.
+ move=> hsem. by inversion hsem; subst; (try discriminate).
move=> [].
+ move=> c /=.
(* empty *)
+ move=> hsem. inversion hsem; subst; (try discriminate). 
  by rewrite /build_i_leakage_spec /extract_declassify_leakages_spec /=.
(* assgn *)
+ move=> x d' e c hsem. inversion hsem; subst; (try discriminate).
  case: H=> h1 h2 h3 h4; subst.
  rewrite /build_i_leakage_spec /=. by case: d0 hsem=> hsem /=.
(* load *)
+ move=> x d' a c hsem. inversion hsem; subst; (try discriminate).
  case: H=> h1 h2 h3 h4; subst.
  rewrite /build_i_leakage_spec /=. by case: d0 hsem=> hsem /=.
(* store *)
+ move=> x d' a c hsem. inversion hsem; subst; (try discriminate).
  case: H=> h1 h2 h3 h4; subst.
  rewrite /build_i_leakage_spec /=. by case: d0 hsem=> hsem /=.
(* cond *)
+ move=> b c c1' c2' hsem. inversion hsem; subst; (try discriminate).
  case: H=> h1 h2 h3 h4; subst. by rewrite /build_i_leakage_spec /=. 
(* protect *)
move=> x y c hsem. inversion hsem; subst; (try discriminate).
case: H=> h1 h2 h3; subst. by rewrite /build_i_leakage_spec /=.
Qed.

Lemma build_empty_c_leakage : forall r1 m1 ms1 ov,
build_c_leakage_spec {| scmd := [::]; rmap := r1; mmap := m1; ms := ms1 |} ov [::] [::].
Proof.
move=> r1 m1 ms1 ov /=. case: ov=> //=.
+ by constructor.
move=> v vs /=. by constructor.
Qed.

Lemma build_empty_dvalue_leakage : forall s1,
build_c_leakage_spec s1 [::] [::] [::].
Proof.
move=> s1. case: s1=> //=.
move=> c r m ms /=. case: c=> //=.
+ by constructor.
move=> v vs /=. by constructor.
Qed.

Lemma step_declassify_state_equiv_spec : forall VGamma AGamma c s1 s2 d ov s1' s2',
type_cmd VGamma AGamma c ->
s1.(scmd) = c ->
state_equiv_spec s1 s2 VGamma AGamma ->
build_state_instr_spec s1 ov d s1' ->
build_state_instr_spec s2 ov d s2' ->
state_equiv_spec s1' s2' VGamma AGamma.
Proof.
move=> VGamma AGamma c [] st1 r1 m1 ms1 [] st2 r2 m2 ms2 dir ov s1' s2' /= hty hc hequiv.
have hequiv' := hequiv.
move: hequiv=> [] /= hst hms hr hm. 
move: r1 m1 ms1 r2 m2 ms2 dir ov s1' s2' hms hr hm hequiv'; subst.
induction hty; subst.
+ induction H; rewrite /=.
  (* Iempty *)
  + move=> r1 m1 ms1 r2 m2 ms2 dir ov s1' s2' hms hr hm hequiv' hb1 hb2.
    inversion hb1; (try discriminate); subst.
    inversion hb2; (try discriminate); subst.
    by apply st_equiv_spec.
(* x := e *)
+ move=> r1 m1 ms1 r2 m2 ms2 dir ov s1 s2' hms hr hm hequiv' hb1 hb2 /=.
  inversion hb1; (try discriminate); subst.
  inversion hb2; (try discriminate); subst.
  apply st_equiv_spec. 
  + by auto.
  + by auto.
  + case: d H1 IHhty hequiv' hb1 hb2 => //=.
    + case: T H=> //=.
      move=> hx _ IHhty hequiv' hb1 hb2 x' hx' /=.
      rewrite /update_rmap /update_map. case: ifP=> /=.
      + by move=> hxeq.
      move=> hxneq. by move: (hr x' hx').
    move=> H1 IHhty hequiv' hb1 hb2 x' hx' /=. 
    rewrite /update_rmap /update_map. case: ifP=> //=.
    + move=> hxeq. apply eqb_eq in hxeq; subst.
      rewrite H in hx'. case: hx'=> hx''; subst.
      apply sub_public_always_public in H1; subst. have hpub : Public = Public. + by auto.
      by have /= := expr_equiv_val_public {| scmd := Iassgn x' false e :: c; rmap := r1; mmap := m1; ms := ms2 |} 
              {| scmd := Iassgn x' false e :: c; rmap := r2; mmap := m2; ms := ms2 |} hr H0 hpub.
    move=> hxneq. by move: (hr x' hx').
  move=> /= hms'. case: d H1 IHhty hequiv' hb1 hb2 => //=.
  + case: T H=> //=.
    + move=> hx _ IHhty hequiv' hb1 hb2 /=. split=> //=.
      + rewrite /update_rmap /update_map /=. move=> x' hx'.
        case: ifP=> //=. move=> hneq. move: (hm hms')=> [] hr' hm'.
        by move: (hr' x' hx').
      move=> a ha. move: (hm hms')=> [] hr' hm'. by move: (hm' a ha).
  move=> H1 IHhty hequiv'. split=> //=.
  + move=> x' hx'. rewrite /update_rmap /update_map. case: ifP=> //=.
    + move=> hxeq. apply eqb_eq in hxeq; subst. rewrite H in hx'.
      case: hx'=> [] ht; subst. apply sub_publicload_public in H1; subst.
      have hpub : Public = Public. + by auto.
      by have /= := expr_equiv_val_public {| scmd := Iassgn x' false e :: c; rmap := r1; mmap := m1; ms := ms2 |} 
              {| scmd := Iassgn x' false e :: c; rmap := r2; mmap := m2; ms := ms2 |} hr H0 hpub.
    move=> hxneq. move: (hm hms')=> [] hr' hm'. by move: (hr' x' hx').
  move=> a ha. move: (hm hms')=> [] hr' hm'. by move: (hm' a ha).
(* x := a[e] *)
+ move=> r1 m1 ms1 r2 m2 ms2 dir ov s1' s2' hms hr hm hequiv' hb1 hb2 /=. 
  case: a H0 IHhty hequiv' hb1 hb2=> //=.
  move=> x' ei hta IHhty hequiv' hb1 hb2 /=.
  inversion hb1; (try discriminate); subst.
  inversion hb2; (try discriminate); subst.
  apply st_equiv_spec.
  + by auto.
  + by auto.
  + move=> x'' hr' /=. inversion hta; (try discriminate); subst.
    case: d H1 IHhty hequiv' hb1 hb2 H11 => //=.
    + case: T H=> //=. move=> hx _ IHhty hequiv' /=. 
      rewrite /update_rmap /update_map /=. 
      case: ifP=> //=. move=> hneq. by move: (hr x'' hr').
    move=> H1 IHhty hequiv'. 
    rewrite /update_rmap /update_map. case: ifP=> //=.
    + move=> hxeq. apply eqb_eq in hxeq; subst. rewrite H in hr'. case: hr'=> h1; subst.
      apply sub_publicload_public in H1; subst. by case: T' hta H3 H1=> //=.
    move=> hneq. by move: (hr x'' hr').
  move=> /= hms1. case: d H1 IHhty hequiv' hb1 hb2 H11 => //. 
  + move=> H1 IHhty hequiv' /=. split=> //=.
    + move=> x'' hx''. rewrite /update_rmap /update_map /=. case: ifP=> //=.
      move=> hneq. move: (hm hms1)=> [] hr' hm'. by move: (hr' x'' hx'').
    move=> a ha. move: (hm hms1)=> [] hr' hm'. by move: (hm' a ha).
  move=> H1 IHhty hequiv' /=. split=> //=.
  + move=> x'' hx''. rewrite /update_rmap /update_map /=. case: ifP=> //=.
    + move=> heq. move: (hm hms1)=> [] hr' hm'. apply eqb_eq in heq; subst.
      rewrite H in hx''. case: hx''=> h1; subst. inversion hta; (try discriminate); subst.
      rewrite H11 /=.
      apply sub_publicload_public in H1. by case: T' hta H1 H3=> //=.
    move=> hneq. move: (hm hms1)=> [] hr' hm'. by move: (hr' x'' hx'').
  move=> a ha. move: (hm hms1)=> [] hr' hm'. by move: (hm' a ha).
(* a[e] := e *)
+ move=> r1 m1 ms1 r2 m2 ms2 dir ov s1' s2' hms hr hm hequiv' hb1 hb2 /=.
  case: a H0 IHhty hequiv' hb1 hb2=> //=.
  move=> x' ei hta IHhty hequiv' hb1 hb2 /=.
  inversion hb1; (try discriminate); subst.
  inversion hb2; (try discriminate); subst.
  apply st_equiv_spec.
  + by auto.
  + by auto.
  + move=> x'' hr' /=. inversion hta; (try discriminate); subst.
    case: d H1 IHhty hequiv' hb1 hb2 H11=> //=.
    + case: T H=> //=. 
      + move=> hx _ IHhty hequiv' /=. by move: (hr x'' hr').
      move=> H. case: T' hta H3=> //= hta H3 _ IHhty hequiv'. by move: (hr x'' hr').
    move=> H. case: T' hta H3=> //= hta H3 _ IHhty hequiv'. by move: (hr x'' hr').
    move=> H1 IHhty hequiv'. by move: (hr x'' hr').
  move=> /= hms1. split=> //=.
  + move=> x'' hx''. move: (hm hms1)=> [] hr' hm'. by move: (hr' x'' hx'').
  move=> a ha /=. case: d H1 IHhty hequiv' hb1 hb2 H11=> //=.
  + case: T' hta=> //= hta _ IHhty hequiv' /=.
    inversion hta; (try discriminate); subst.
    rewrite /update_mem /update_map /=. case: ifP=> //=.
    + move=> heq. apply eqb_eq in heq; subst.
      rewrite ha in H2. by case: H2.
    move=> hneq. move: (hm hms1)=> [] hr' hm'. by move: (hm' a ha).
  move=> H1 Ihhty hequiv' /=. move: (hm hms1)=> [] hr' hm'.
  rewrite /update_mem /update_map /=. case: ifP=> //=.
  + move=> heq. apply eqb_eq in heq; subst.
    move: (hm' a ha)=> ->. inversion hta; (try discriminate); subst.
    rewrite ha in H3. case: H3=> h3; subst.
    have hpub : Public = Public. + by auto.
    have -> := expr_equiv_val_public {| scmd := Istore (AA a ei) false e :: c; rmap := r1; mmap := m1; ms := ms2 |}
          {| scmd := Istore (AA a ei) false e :: c; rmap := r2; mmap := m2; ms := ms2 |} hr H5 hpub.
    case: T H1 H=> //= _ H1. 
    by have -> := expr_equiv_val_public {| scmd := Istore (AA a ei) false e :: c; rmap := r1; mmap := m1; ms := ms2 |}
          {| scmd := Istore (AA a ei) false e :: c; rmap := r2; mmap := m2; ms := ms2 |} hr H1 hpub.
  move=> hneq. by move: (hm' a ha).
(* If b i i' *)
+ move=> r1 m1 ms1 r2 m2 ms2 dir ov s1' s2' hms hr hm hequiv' hb1 hb2 /=. 
  case: b H0 H IHhty hequiv' hb1 hb2 => //=.
  move=> bop e e' hity hbty IHhty hequiv' hb1 hb2 /=. 
  inversion hb1; (try discriminate); subst.
  inversion hb2; (try discriminate); subst.
  inversion hbty; (try discriminate); subst.
  apply union_public_eq in H4. case: H4=> h4 h5; subst.
  apply st_equiv_spec. + by auto. 
  + rewrite /=. have hpub : Public = Public. + by auto.
    have -> := expr_equiv_val_public {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r1; mmap := m1; ms := ms2 |}
            {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r2; mmap := m2; ms := ms2 |} hr H2 hpub.
    by have -> := expr_equiv_val_public {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r1; mmap := m1; ms := ms2 |}
            {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r2; mmap := m2; ms := ms2 |} hr H5 hpub.
  + move=> x hx /=. by move: (hr x hx).
  + move=> /= hms'. split=> //=.
    + move=> x hx. have hpub : Public = Public. + by auto.
    have he := expr_equiv_val_public {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r1; mmap := m1; ms := ms2 |}
            {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r2; mmap := m2; ms := ms2 |} hr H2 hpub.
    have he' := expr_equiv_val_public {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r1; mmap := m1; ms := ms2 |}
            {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r2; mmap := m2; ms := ms2 |} hr H5 hpub.
    rewrite he he' /= in hms'. move: hms'. case: ifP=> //= heval hms'.
    move: (hm hms')=> [] hr' hm'. by move: (hr' x hx).
  move=> a ha.  have hpub : Public = Public. + by auto.
  have he := expr_equiv_val_public {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r1; mmap := m1; ms := ms2 |}
            {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r2; mmap := m2; ms := ms2 |} hr H2 hpub.
  have he' := expr_equiv_val_public {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r1; mmap := m1; ms := ms2 |}
            {| scmd := Iif (Ebool bop e e') i i' :: c; rmap := r2; mmap := m2; ms := ms2 |} hr H5 hpub.
  rewrite he he' /= in hms'. move: hms'. case: ifP=> //= heval hms'. move: (hm hms')=> [] hr' hm'.
  by move: (hm' a ha).
(* Protect x y *)
+ move=> r1 m1 ms1 r2 m2 ms2 ov dir s1' s2' hms hr hm hequiv' hb1 hb2 /=.
  inversion hb1; (try discriminate); subst.
  inversion hb2; (try discriminate); subst.
  apply st_equiv_spec.
  + by auto.
  + by auto.
  + move=> x' hx' /=. case: ms2 hm hequiv' hb1 hb2=> //=.
    + move=> hms hm hequiv'; subst.
      rewrite /update_rmap /update_map. case: ifP=> //=.
      move=> hneq. by move: (hr x' hx').
    move=> hms hm hequiv'; subst. rewrite /update_rmap /update_map /=.
    case: ifP=> //=.
    + move=> heq. apply eqb_eq in heq; subst. apply sub_publicload_public in H1; subst.
      by move: (hr y H0).
    move=> hneq. by move: (hr x' hx').
  move=> /= hms1. split=> //=.
  + move=> x' hx'. case: ifP=> //=.
    + move=> hms1'; subst. move: (hm hms1)=> [] hr' hm'.
      rewrite /update_rmap /update_map. case: ifP=> //=.
      + move=> heq. apply eqb_eq in heq; subst. apply sub_publicload_public in H1; subst.
        by move: (hr y H0).
      move=> hneq. by move: (hr' x' hx').
    move=> a ha. move: (hm hms1)=> [] hr' hm'. by move: (hm' a ha).
move=> r1 m1 ms1 r2 m2 ms2 dir ov /= s1' s2' hms hr hm hequiv hb1 hb2 /=; subst. 
by inversion hb1; (try discriminate); subst. 
Qed.

Lemma st_show_spec : forall s,
{| scmd := scmd s; rmap := rmap s; mmap := mmap s; ms := ms s |} = s. 
Proof.
move=> s. by case: s.
Qed.

Lemma step_to_build_state_spec : forall s d l s',
sem_instr_spec s d l s' ->
build_state_instr_spec s (extract_declassify_leakages_spec l) d s'.
Proof.
move=> [] c r1 m1 ms1 d l s' hstep.
case: c hstep=> //=.
+move=> hstep. by inversion hstep; (try discriminate); subst.
move=> i c hstep. case: i hstep=> //=.
(* Iempty *)
+ move=> hstep. inversion hstep; (try discriminate); subst; rewrite /=.
  inversion H; (try discriminate); subst. by constructor.
(* x := e *)
+ move=> x d' e hstep. case: d' hstep=> //=.
  + move=> hstep. inversion hstep; (try discriminate); subst.
    case: d0 hstep H=> //= hstep [] h1 h2 h3; subst. by constructor.
  move=> hstep. inversion hstep; (try discriminate); subst; rewrite /=.
  case: d0 hstep H=> //= hstep [] h1 h2 h3; subst. by constructor.
(* x := a[e] *)
+ move=> x d' a hstep. case: d' hstep=> //=.
  + move=> hstep. inversion hstep; (try discriminate); subst.
    case: d0 hstep H=> //= hstep [] h1 h2 h3; subst. by constructor.
  move=> hstep. inversion hstep; (try discriminate); subst; rewrite /=.
  case: d0 hstep H=> //= hstep [] h1 h2 h3; subst. by constructor.
(* a[e] := e *)
+ move=> x d' e hstep. case: d' hstep=> //=.
  + move=> hstep. inversion hstep; (try discriminate); subst.
    case: d0 hstep H=> //= hstep [] h1 h2 h3; subst. by constructor.
  move=> hstep. inversion hstep; (try discriminate); subst; rewrite /=.
  case: d0 hstep H=> //= hstep [] h1 h2 h3; subst. by constructor.
(* if b i i' *)
+ move=> b i i' hstep. case: b hstep=> //= bop e e' hstep.
  inversion hstep; (try discriminate); subst; rewrite /=. 
  inversion H; (try discriminate); subst.
  by apply build_next_if.
(* protect x y *)
move=> x y hstep /=. inversion hstep; (try discriminate); subst; rewrite /=.
inversion H; (try discriminate); subst. by constructor.
Qed.

Lemma preservation_without_semantic_spec : forall VGamma AGamma s ov d s',
type_cmd VGamma AGamma s.(scmd) ->
build_state_instr_spec s ov d s' -> 
type_cmd VGamma AGamma s'.(scmd).
Proof.
move=> VGamma AGamma [] c r m ms ov d s' /= hty hnext.
case: c hty hnext=> //=.
+ move=> hty hnext. by inversion hnext; (try discriminate); subst.
move=> i c hi hnext. 
case:i hi hnext=> //=.
+ move=> hi hnext. inversion hnext; (try discriminate); subst; rewrite /=.
  by inversion hi; (try discriminate); subst.
+ move=> x d' e hi hnext. inversion hnext; (try discriminate); subst; rewrite /=.
  by inversion hi; (try discriminate); subst.
+ move=> x d' a hi hnext. inversion hnext; (try discriminate); subst; rewrite /=.
  by inversion hi; (try discriminate); subst.
+ move=> a d' e hi hnext. inversion hnext; (try discriminate); subst; rewrite /=.
  by inversion hi; (try discriminate); subst.
+ move=> b i i' hi hnext. inversion hnext; (try discriminate); subst; rewrite /=.
  inversion hi; (try discriminate); subst. inversion H1; (try discriminate); subst.
  apply type_concat=> //=. by case: ifP.
move=> x y hi hnext. inversion hnext; (try discriminate); subst; rewrite /=.
by inversion hi; (try discriminate); subst.
Qed.

Lemma declassify_mem_to_leakages : forall VGamma AGamma c,
type_cmd VGamma AGamma c -> 
(forall s1 s2 ov ls1 ls2 ds, 
   c = s1.(scmd) ->
   state_equiv_spec s1 s2 VGamma AGamma ->
   build_c_leakage_spec s1 ov ds ls1 ->
   build_c_leakage_spec s2 ov ds ls2 ->
   ls1 = ls2).
Proof.
move=> VGamma AGamma c hty.
move=> [] c1 r1 m1 ms1 [] c2 r2 m2 ms2 ov ls1 ls2 ds hc hequiv /=; subst. 
move: hequiv=> [] /= hst /= hms hr hm; subst. rewrite /= in hty.
move: c2 r1 m1 r2 m2 ls1 ls2 ds ms2 hm hr hty.
induction ov.
(* ov = [::] *)
+ move=> c2 r1 m1 r2 m2 ms2 hm hr hty.
  case: c2 hm hr hty=> //=.
  + move=> ls1 ls2 ds hm hr hty h1 h2.
    inversion h1; (try discriminate); subst. + by inversion h2; (try discriminate); subst.
    + by inversion h2; (try discriminate); subst.
  move=> i c ls1 ls2 ds hm hr hty h1 h2. inversion h1; (try discriminate); subst. 
  by inversion h2; (try discriminate); subst.
move=> c2 r1 m1 r2 m2 ls1 ls2 ds hm hr hty.
case: c2 hm hr hty=> /=.
(* empty seq of instructions *)
+ move=> hms hm hr hty h1 h2. inversion h1; (try discriminate); subst. by inversion h2; (try discriminate); subst.
(* i :: c *)
move=> i c ms hm hr /= hty h1 h2; rewrite /=. have h1' := h1. have h2' := h2.
inversion h1; (try discriminate); subst. inversion h2; (try discriminate); subst.
have heq : scmd {| scmd := i :: c; rmap := r1; mmap := m1; ms := ms |} = i :: c. + by auto.
have heq' : i :: c = scmd {| scmd := i :: c; rmap := r1; mmap := m1; ms := ms |}. + by auto.
have hequiv : state_equiv_spec {| scmd := i :: c; rmap := r1; mmap := m1; ms := ms |}
              {| scmd := i :: c; rmap := r2; mmap := m2; ms := ms |} VGamma AGamma.
+ apply st_equiv_spec; by auto.
have hsteq := step_declassify_state_equiv_spec.
move: (hsteq VGamma AGamma (i::c) {| scmd := i :: c; rmap := r1; mmap := m1; ms := ms |}
{| scmd := i :: c; rmap := r2; mmap := m2; ms := ms |} d a s' s'0 hty heq hequiv H9 H12)=> hequiv'.
move: hequiv'=> [] hst hms hr' hm'. rewrite -heq in hty.
have hty' := preservation_without_semantic_spec hty H9. 
case: s' H9 H10 hm' hst hms hr' hty'=> s1' r1' m1' ms1' H9 /= H10 /= hm' hst hms /= hr' hty'; subst. 
case: s'0 H9 H10 H12 H13 hm' hr' hty'=> s2' r2' m2' ms2' H9 H10 H12 H13 /= hm' /= hr' hty'; subst. rewrite /= in H9.
move: (IHov s2' r1' m1' r2' m2' ls ls0 ds0 ms2' hm' hr' hty' H10 H13)=> ->. 
by have -> := declassify_mem_to_leakage_spec hty a heq' hequiv.
Qed.

Lemma declassify_to_leakage_c : forall VGamma AGamma c,
type_cmd VGamma AGamma c ->
(forall s1 s1' n d l, 
 c = s1.(scmd) ->
 multi_step_spec s1 d l n s1' -> 
 build_c_leakage_spec s1 (extract_declassify_leakagess_spec l) d l).
Proof.
move=> VGamma AGamma c /= hty.
move=> [] c1 r1 m1 ms1 s1' n d l hc hmulti; subst. 
move: c1 r1 m1 ms1 s1' d l hmulti hty.
induction n.
(* n = 0 *)
+ move=> c1 r1 m1 ms1 s1' d l hmulti hty /=.
  (* 0 step means s1 = s1' and no leakage [::] *)
  inversion hmulti; (try discriminate); subst; rewrite /=.
  + case: c1 hmulti hty. + move=> hmulti hty. by constructor.
  move=> i c hmulti hty. by constructor.
  by case: (n) H=> //=.
(* n != 0 *)
move=> c1 r1 m1 ms1 s1' d l hmulti hty.
rewrite -addn1 in hmulti. 
inversion hmulti; (try discriminate); subst.
(* empty leakage *)
+ by case: n H3 IHn hmulti=> //=.
(* non-empty leakage *)
case: c1 hty hmulti H0=> //=.
(* empty seq of instructions *)
+ move=> hty hmulti hsem.
  inversion hmulti; (try discriminate); subst.
  by inversion H8; (try discriminate); subst.
(* i :: c *)
move=> i c hty hmulti H0 /=.
inversion hmulti; (try discriminate); subst.
apply PeanoNat.Nat.add_cancel_r in H; rewrite H in H4.
apply PeanoNat.Nat.add_cancel_r in H8 ; subst.
have heq : i :: c = {| scmd := i :: c; rmap := r1; mmap := m1; ms := ms1 |}.(scmd). + by auto.
have heq' : {| scmd := i :: c; rmap := r1; mmap := m1; ms := ms1 |}.(scmd) = i :: c. + by auto.
have hnext : build_state_instr_spec {| scmd := i :: c; rmap := r1; mmap := m1; ms := ms1 |} 
                   (extract_declassify_leakages_spec l0) d0 s'0.
+ by have := step_to_build_state_spec H9. 
have hi := declassify_to_leakage_i_spec heq H9.
rewrite heq in hty.
have hty' := preservation_without_semantic_spec hty hnext.
apply build_leakage_seq_c_vs with s'0.
+ by apply hi.
+ by apply hnext.
case: s'0 H9 H10 hnext hty'=> //= s2 r2 m2 ms H9 H10 hnext hty'.
by move: (IHn s2 r2 m2 ms s1' d' l' H10 hty').
Qed.

Lemma type_declassify_ct_to_ct_spec : forall VGamma AGamma s1 s2,
type_cmd VGamma AGamma s1.(scmd) /\ constant_time_declassify_spec VGamma AGamma s1 s2 ->
constant_time_spec VGamma AGamma s1 s2.
Proof.
move=> VGamma AGamma s1 s2 hty. rewrite /constant_time_spec /=.
case: hty=> [] hty hdeclassify. rewrite /constant_time_declassify_spec in hdeclassify.
move=> s1' s2' d l1 l2 n hequiv hmulti hmulti'.
move: (hdeclassify s1' s2' d l1 l2 n hequiv hmulti hmulti')=> [] hdeq hsafe {hdeclassify}.
split; last by split=> //= hst; apply safe_lang.
move: s1 s2 d l1 l2 hmulti hmulti' hequiv hty hdeq.
induction n.
(* n = 0 *)
+ move=> s1 s2 d l1 l2 hmulti hmulti' hequiv hty hdeq.
  inversion hmulti; (try discriminate); subst.
  inversion hmulti'; (try discriminate); subst; auto.
  by case:(n) H.
move=> s1 s2 d l1 l2 hmulti hmulti' hequiv hty hdeq. 
inversion hmulti; (try discriminate); subst.
inversion hmulti'; (try discriminate); subst; auto.
have hd:= declassify_to_leakage_i_spec. have heq : forall s, scmd s = scmd s. + by auto.
move: (hd s1 s' d0 l (scmd s1) (heq s1) H0)=> <- /=.
have hequiv' := hequiv.
case: hequiv=> [] hst hms hr hm. rewrite hst in hty.
move: (hd s2 s'0 d0 l0 (scmd s2) (heq s2) H7)=> <- /=.
case: hdeq=> hd1 hds1. rewrite hd1.
rewrite addn1 in H5. case: H5=> h1; subst.
rewrite addn1 in H. case: H=> h; subst.
have hequiv'' := step_declassify_state_equiv_spec hty hst hequiv'.
have hs1eq := step_to_build_state_spec H0. rewrite hd1 in hs1eq.
have hs2eq := step_to_build_state_spec H7. 
rewrite -hst in hty.
have hty' := preservation hty H0.
move: (hequiv'' d0 (extract_declassify_leakages_spec l0) s' s'0 hs1eq hs2eq)=> {hequiv''} hequiv''. 
move: (IHn s' s'0 d' l' l'0 H4 H9 hequiv'' hty' hds1)=> ->.
by have -> := declassify_mem_to_leakage_spec hty (extract_declassify_leakages_spec l0) (heq s1) hequiv'.
Qed.




