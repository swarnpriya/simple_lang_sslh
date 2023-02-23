Require Import Nat.
Require Import String.
Require Import List.
From mathcomp Require Import all_ssreflect all_algebra.
From LF Require Export lang_declassify type_declassify.

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

Definition extract_declassify_leakage (l : leakage) : option value :=
match l with 
 | Ldeclassify v => v
 | _ => None
end. 

Fixpoint extract_declassify_leakages (l : seq leakage) : seq (option value) :=
match l with 
 | [::] => [::]
 | l :: ls => extract_declassify_leakage l :: extract_declassify_leakages ls
end.

Fixpoint extract_declassify_leakagess (l : seq (seq leakage)) : seq (seq (option value)) :=
match l with 
 | [::] => [::]
 | l :: ls => extract_declassify_leakages l :: extract_declassify_leakagess ls
end.

Definition dummy_value : option value := None.

Definition constant_time_declassify (VGamma:venv) (AGamma:aenv) (s1 s2:state_sf) := forall s1' s2' l1 l2 n,
state_equiv s1 s2 VGamma AGamma ->
multi_step s1 l1 n s1' ->
multi_step s2 l2 n s2' ->
extract_declassify_leakagess l1 = extract_declassify_leakagess l2 /\
(safe_state s1' <-> safe_state s2').

Lemma progress : forall VGamma AGamma s,
type_cmd VGamma AGamma s.(scmd_sf) ->
safe_state s.
Proof.
move=> VGamma AGamma [] /= []. 
(* empty *)
+ by left.
(* i::c *)
move=> i c r m hty. induction hty. induction H.
(* empty *)
+ right. exists [::]. 
  exists {| scmd_sf := c0; rmap_sf := r; mmap_sf := m |}. by apply Iempty_sem.
(* x := e:: c*)
+ right.
  exists (if d then [:: Ldeclassify (Some (sem_expr {| scmd_sf := Iassgn x d e :: c0; rmap_sf := r; mmap_sf := m |} e))] else [:: Lempty]).
  exists {| scmd_sf := c0; 
            rmap_sf := update_rmap r x 
                       (sem_expr {| scmd_sf := Iassgn x d e :: c0; rmap_sf := r; mmap_sf := m |} e);
            mmap_sf := m |}.
  by apply Iassgn_sem.
(* x := a[e]::c *)
+ case: a H0=> a e H0. right.
  exists  (if d then [:: Lindex (sem_expr {| scmd_sf := Iload x d (AA a e) :: c0; rmap_sf := r; mmap_sf := m |} e); 
                         Ldeclassify (Some (Array.get (mmap_sf {| scmd_sf := Iload x d (AA a e) :: c0; rmap_sf := r; mmap_sf := m |} a) 
                                     (sem_expr {| scmd_sf := Iload x d (AA a e) :: c0; rmap_sf := r; mmap_sf := m |} e)))]
                else [:: Lindex (sem_expr {| scmd_sf := Iload x d (AA a e) :: c0; rmap_sf := r; mmap_sf := m |} e)]).
  exists {| scmd_sf := c0; 
            rmap_sf := update_rmap r x 
                       (Array.get (mmap_sf {| scmd_sf := Iload x d (AA a e) :: c0; rmap_sf := r; mmap_sf := m |} a) 
                       (sem_expr {| scmd_sf := Iload x d (AA a e) :: c0; rmap_sf := r; mmap_sf := m |} e));
            mmap_sf := m |}.
  by apply Iload_sem.
(* a[e] := e *)
+ case: a H0=> a ei H0. right. 
  exists (if d then [:: Lindex (sem_expr {| scmd_sf := Istore (AA a ei) d e :: c0; rmap_sf := r; mmap_sf := m |} ei); 
                        Ldeclassify (Some (sem_expr {| scmd_sf := Istore (AA a ei) d e :: c0; rmap_sf := r; mmap_sf := m |} e))] 
               else [:: Lindex (sem_expr {| scmd_sf := Istore (AA a ei) d e :: c0; rmap_sf := r; mmap_sf := m |} ei)]).
  exists {| scmd_sf := c0; 
            rmap_sf := r;
            mmap_sf := update_mem m a 
                       (sem_expr {| scmd_sf := Istore (AA a ei) d e :: c0; rmap_sf := r; mmap_sf := m |} ei) 
                       (sem_expr {| scmd_sf := Istore (AA a ei) d e :: c0; rmap_sf := r; mmap_sf := m |} e) |}.  
  by apply Istore_sem. 
(* if b i1 i2 *)
+ case: b H=> b e1 e2 H. right.
  exists [:: (Lbool (eval_bool_op b 
                (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i0 i' :: c0; rmap_sf := r; mmap_sf := m |} e1) 
                (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i0 i' :: c0; rmap_sf := r; mmap_sf := m |} e2)))].
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
Lemma safe_lang : forall s,
safe_state s.
Proof.
rewrite /safe_state /= /final_state /=.
move=> [] st r m /=. case: st=> //=.
+ by left.
move=> i c. case: i.
(* empty *)
+ right.
  exists [::]. 
  exists {| scmd_sf := c; rmap_sf := r; mmap_sf := m |}. by apply Iempty_sem.
(* x := e *)
+ move=> x d e. right. 
  exists (if d then [:: Ldeclassify (Some (sem_expr {| scmd_sf := Iassgn x d e :: c; rmap_sf := r; mmap_sf := m |} e))] else [:: Lempty]). 
  exists {| scmd_sf := c; 
            rmap_sf := update_rmap r x 
                       (sem_expr {| scmd_sf := Iassgn x d e :: c; rmap_sf := r; mmap_sf := m |} e);
            mmap_sf := m |}.
  by apply Iassgn_sem.
(* x := a[e]::c *)
+ move=> x d [] a e. right.
  exists (if d then [:: Lindex (sem_expr {| scmd_sf := Iload x d (AA a e) :: c; rmap_sf := r; mmap_sf := m |} e); 
                         Ldeclassify (Some (Array.get (mmap_sf {| scmd_sf := Iload x d (AA a e) :: c; rmap_sf := r; mmap_sf := m |} a) 
                                     (sem_expr {| scmd_sf := Iload x d (AA a e) :: c; rmap_sf := r; mmap_sf := m |} e)))]
                else [:: Lindex (sem_expr {| scmd_sf := Iload x d (AA a e) :: c; rmap_sf := r; mmap_sf := m |} e)]).
  exists {| scmd_sf := c; 
            rmap_sf := update_rmap r x 
                       (Array.get (mmap_sf {| scmd_sf := Iload x d (AA a e) :: c; rmap_sf := r; mmap_sf := m |} a) 
                       (sem_expr {| scmd_sf := Iload x d (AA a e) :: c; rmap_sf := r; mmap_sf := m |} e));
            mmap_sf := m |}.
  by apply Iload_sem.
(* a[e] := e *)
+ move=> [] a ei. right. 
  exists (if d then [:: Lindex (sem_expr {| scmd_sf := Istore (AA a ei) d e :: c; rmap_sf := r; mmap_sf := m |} ei); 
                        Ldeclassify (Some (sem_expr {| scmd_sf := Istore (AA a ei) d e :: c; rmap_sf := r; mmap_sf := m |} e))] 
               else [:: Lindex (sem_expr {| scmd_sf := Istore (AA a ei) d e :: c; rmap_sf := r; mmap_sf := m |} ei)]).
  exists {| scmd_sf := c; 
            rmap_sf := r;
            mmap_sf := update_mem m a 
                       (sem_expr {| scmd_sf := Istore (AA a ei) d e :: c; rmap_sf := r; mmap_sf := m |} ei) 
                       (sem_expr {| scmd_sf := Istore (AA a ei) d e :: c; rmap_sf := r; mmap_sf := m |} e) |}.  
  by apply Istore_sem. 
(* if b i1 i2 *)
+ move=> [] b e1 e2 i i'. right.
  exists [:: (Lbool (eval_bool_op b 
                (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i i' :: c; rmap_sf := r; mmap_sf := m |} e1) 
                (sem_expr {| scmd_sf := Iif (Ebool b e1 e2) i i' :: c; rmap_sf := r; mmap_sf := m |} e2)))].
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
+ rewrite H /= in hty. by inversion hty; subst. 
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

Definition declassify_val (d:bool) ve (v : seq (option value)) : value := 
  if d then (odflt 0 (last None v))
  else ve.

Definition build_i_leakage (s: state_sf) (v : seq (option value)) : seq leakage :=
match (nth Iempty (scmd_sf s) 0) with 
 | Iempty => [::]
 | Iassgn x d e => if d then [:: Ldeclassify (nth dummy_value v 0)] else [:: Lempty]
 | Iload x d (AA a e) => if d then [:: Lindex (sem_expr s e); Ldeclassify (nth dummy_value v 1)]
                              else [:: Lindex (sem_expr s e)]
 | Istore (AA a e) d e' => if d then [:: Lindex (sem_expr s e); Ldeclassify (nth dummy_value v 1)] 
                                else [:: Lindex (sem_expr s e)] 
 | Iif (Ebool bop e1 e2) i1 i2 => [:: Lbool (eval_bool_op bop (sem_expr s e1) (sem_expr s e2))]
end. 

Definition build_state_instr (s : state_sf) (vs : seq (option value)) : state_sf := 
match (nth Iempty (scmd_sf s) 0) with 
 | Iempty => {| scmd_sf := (tl s.(scmd_sf)); 
                rmap_sf := rmap_sf s; 
                mmap_sf := mmap_sf s |} 
 | Iassgn x d e => {| scmd_sf := (tl s.(scmd_sf)); 
                      rmap_sf := update_rmap (rmap_sf s) x (declassify_val d (sem_expr s e) vs); 
                      mmap_sf := mmap_sf s |} 
 | Iload x d (AA a e) => {| scmd_sf := (tl s.(scmd_sf)); 
                            rmap_sf := update_rmap (rmap_sf s) x (declassify_val d (Array.get (mmap_sf s a)(sem_expr s e)) vs);
                            mmap_sf := mmap_sf s |}
 | Istore (AA a e) d e' => {| scmd_sf := (tl s.(scmd_sf)); 
                              rmap_sf := rmap_sf s;
                              mmap_sf := update_mem (mmap_sf s) a (sem_expr s e) (declassify_val d (sem_expr s e') vs) |} 
 | Iif (Ebool bop e1 e2) i1 i2 =>  {| scmd_sf := (if eval_bool_op bop (sem_expr s e1) (sem_expr s e2)
                                                  then i1
                                                  else i2) ++ (tl s.(scmd_sf));
                                      rmap_sf := rmap_sf s;
                                      mmap_sf := mmap_sf s |}
end.

Fixpoint build_c_leakage (s: state_sf) (vs : seq (seq (option value))) : seq (seq leakage) :=
match s.(scmd_sf), vs with 
 | [::], [::] => [::]
 | i::c, v :: vs => build_i_leakage s v :: 
                    build_c_leakage (build_state_instr s v) vs
 | _, _ => [::]
end.

Lemma declassify_mem_to_leakage : forall VGamma AGamma c,
type_cmd VGamma AGamma c ->
(forall s1 s2 ov, 
   c = s1.(scmd_sf) ->
   state_equiv s1 s2 VGamma AGamma ->
   build_i_leakage s1 ov = build_i_leakage s2 ov).
Proof.
move=> VGamma AGamma c hty.
move=> [] st1 r1 m1 [] st2 r2 m2 ov hc hequiv /=; subst. 
move: hequiv=> [] hr hm /==> hst; subst. rewrite /= in hty.
elim: hty; last first. + by auto.
move=> i c htyi htyc hrec. move: r1 m1 hrec hm hr. 
induction htyi.
(* empty *)
+ by move=> r1 m1 /= hrec /= hm hr. 
(* x := e *)
+ by move=> r1 m1 /= hrec hm hr.
(* x := a[e] *)
+ move=> r1 m1 /= hrec hm hr. case: a H0=> //=.
  move=> x' e htya. inversion htya; subst.
  have hpub : Public = Public. + by auto.
  rewrite /build_i_leakage /=.
  by have -> := expr_equiv_val {| scmd_sf := Iload x d (AA x' e) :: c; rmap_sf := r1; mmap_sf := m1 |} {| scmd_sf := Iload x d (AA x' e) :: c; rmap_sf := r2; mmap_sf := m2 |} hr H5 hpub.
(* a[e] := e *)
+ move=> r1 m1 /= hrec hm hr. case: a H0=> //=.
  move=> x' ei htya. inversion htya; subst.
  have hpub : Public = Public. + by auto.
  rewrite /build_i_leakage /=.
  by have -> := expr_equiv_val {| scmd_sf := Istore (AA x' ei) d e :: c; rmap_sf := r1; mmap_sf := m1 |} {| scmd_sf := Istore (AA x' ei) d e :: c; rmap_sf := r2; mmap_sf := m2 |} hr H5 hpub.
(* if e i i' *)
move=> r1 m1 /= hrec hm hr. case: b H=> //= b' e e' hty.
inversion hty; subst. apply union_public_always_public in H5.
case H5=> h5 h6; subst. case: H5=> hpub _.
rewrite /build_i_leakage /=.
have -> := expr_equiv_val {| scmd_sf := Iif (Ebool b' e e') i i' :: c; rmap_sf := r1; mmap_sf := m1 |} {| scmd_sf := Iif (Ebool b' e e') i i' :: c; rmap_sf := r2; mmap_sf := m2 |} hr H3 hpub.
by have -> := expr_equiv_val {| scmd_sf := Iif (Ebool b' e e') i i' :: c; rmap_sf := r1; mmap_sf := m1 |} {| scmd_sf := Iif (Ebool b' e e') i i' :: c; rmap_sf := r2; mmap_sf := m2 |} hr H6 hpub.
Qed.

Lemma declassify_to_leakage_i : forall VGamma AGamma c,
type_cmd VGamma AGamma c ->
(forall s1 s1' l, 
 c = s1.(scmd_sf) -> 
 sem_instr s1 l s1' -> 
 build_i_leakage s1 (extract_declassify_leakages l) = l).
Proof.
move=> VGamma AGamma c /= hty.
elim: hty.
+ move=> i c' hity hcty hrec. 
  induction hity.
  (* empty *)
  + move=> [] st1 r1 m1 s1' l /= hst /= hempty /=; subst.
    by inversion hempty; subst; (try discriminate).
  (* x := e *)
  + move=> [] st1 r1 m1 s1' l /= hst hassgn; rewrite -hst in hassgn. 
    inversion hassgn; (try discriminate); subst.
    case: H2=> /= h1 h2 h3 h4; subst. by case: d0 H1 hassgn=> H1 hassgn /=.
  (* x := a[e] *)
  + move=> [] st1 r1 m1 s1' l /= hst hload; rewrite -hst in hload. 
    inversion hload; subst; (try discriminate).
    case: H2=> h1 h2 h3 h4; subst. by case: d0 H1 hload=> H1 hload /=.
  (* a[e] := e *)
  + move=> [] st1 r1 m1 s1' l /= hst hstore; rewrite -hst in hstore. 
    inversion hstore; subst; (try discriminate).
    case: H2=> h1 h2 h3 h4; subst. by case: d0 H0 hstore H1=> H0 hstore H1 /=.
  (* if b i i' *)
  move=> [] st1 r1 m1 s1' l /= hst hif; rewrite -hst in hif. 
  inversion hif; subst; (try discriminate).
  by case: H2=> h1 h2 h3 h4; subst; rewrite /=. 
move=> [] st1 r1 m1 s1' l /= hst /= hempty; rewrite -hst in hempty.
by inversion hempty; subst; (try discriminate).
Qed.

Lemma build_empty_c_leakage : forall r1 m1 ov,
build_c_leakage {| scmd_sf := [::]; rmap_sf := r1; mmap_sf := m1 |} ov = [::].
Proof.
move=> r1 m1 ov /=. by case: ov=> //=.
Qed.

Lemma build_empty_dvalue_leakage : forall s1,
build_c_leakage s1 [::] = [::].
Proof.
move=> s1. case: s1=> //=.
move=> c r m /=. by case: c=> //=.
Qed.

Lemma step_declassify_state_equiv : forall VGamma AGamma c s1 s2 ov,
type_cmd VGamma AGamma c ->
s1.(scmd_sf) = c ->
state_equiv s1 s2 VGamma AGamma ->
state_equiv (build_state_instr s1 ov) (build_state_instr s2 ov) VGamma AGamma.
Proof.
move=> VGamma AGamma c [] st1 r1 m1 [] st2 r2 m2 ov /= hty hc hequiv.
move: hequiv=> [] hr hm /= hst. 
move: r1 m1 r2 m2 ov hr hm. 
induction hty. rewrite /build_state_instr /=; subst. induction H; rewrite /=.
(* Iempty *)
+ move=> r1 m1 r2 m2 ov hr hm /=.
  apply st_equiv; by auto.
(* x := e *)
+ move=> r1 m1 r2 m2 ov hr hm /=.
  apply st_equiv; last first. + by auto.
  + move=> a ha /=. by move: (hm a ha).
  move=> x' hx' /=. rewrite /update_rmap /update_map.
  case: ifP=> //=.
  + move=> hs /=.  apply eqb_eq in hs; rewrite -hs in hx'.
    rewrite /declassify_val /=. case: d H1 IHhty=> //=.
    move=> hsub hc /=. rewrite H in hx'. case: hx'=> ht; subst.
    have ht := sub_public_always_public T' hsub.
    have hexpr := expr_equiv_val.
    by move: (hexpr VGamma  {| scmd_sf := Iassgn x' false e :: c; rmap_sf := r1; mmap_sf := m1 |}
            {| scmd_sf := Iassgn x' false e :: c; rmap_sf := r2; mmap_sf := m2 |} e T' hr H0 ht).
  move=> hs /=. by move: (hr x' hx').
(* x := a[e] *)
+ move=> r1 m1 r2 m2 ov hr hm /=. case: a H0 IHhty=> //=.
  move=> x' ei hta hc /=.
  apply st_equiv; last first. + by auto.
  + move=> a ha /=. by move: (hm a ha).
  move=> r hr' /=. rewrite /update_rmap /update_map /=.
  case: ifP=> //=.
  + move=> hs. apply eqb_eq in hs; rewrite -hs in hr'.
    rewrite H in hr'. case: hr'=> ht; subst. case: d H1 hc=> //=.
    move=> hsub hrec /=. inversion hta; (try discriminate); subst.
    have ht := sub_public_always_public T' hsub. rewrite ht in H2.
    have hexpr := expr_equiv_val. have hpub : Public = Public. + by auto.
    move: (hexpr VGamma  {| scmd_sf := Iload r false (AA x' ei) :: c; rmap_sf := r1; mmap_sf := m1 |}
    {| scmd_sf := Iload r false (AA x' ei) :: c; rmap_sf := r2; mmap_sf := m2 |} ei Public hr H4 hpub)=> ->.    by move: (hm x' H2)=> ->.
  move=> hs. by move: (hr r hr').
 (* a[e] := e *)
 + move=> r1 m1 r2 m2 ov hr hm. case: a H0 IHhty=> //=.
   move=> x' ei hta hrec. inversion hta; (try discriminate); subst.
   apply st_equiv; last first. + by auto.
   + move=> a ha /=. rewrite /update_mem /update_map.
     case: ifP=> //=.
     + move=> hs. case: d H1 hrec=> //=.
       case: T hta H3=> //=.
       (* declassify + array is secret *)
       + move=> hta hx' _ hrec. inversion hta; (try discriminate); subst.
         apply eqb_eq in hs. rewrite -hs in ha. rewrite H2 in ha. by case: ha.
       (* declassify + array is public *)
       move=> hta hx' _ hrec. apply eqb_eq in hs. rewrite -hs in ha.
       move: (hm x' ha)=> ->.
       have hexpr := expr_equiv_val. have hpub : Public = Public. + by auto.
       by move: (hexpr VGamma {| scmd_sf := Istore (AA x' ei) true e :: c; rmap_sf := r1; mmap_sf := m1 |}
         {| scmd_sf := Istore (AA x' ei) true e :: c; rmap_sf := r2; mmap_sf := m2 |} ei Public hr H5 hpub)
         => -> /=.
     (* no declassify + array is secret *) 
     move=> hsub hrec /=. inversion hta; (try discriminate); subst.
     have hexpr := expr_equiv_val. have hpub : Public = Public. + by auto.
     move: (hexpr VGamma {| scmd_sf := Istore (AA x' ei) false e :: c; rmap_sf := r1; mmap_sf := m1 |}
     {| scmd_sf := Istore (AA x' ei) false e :: c; rmap_sf := r2; mmap_sf := m2 |} ei Public hr H5 hpub)
     => -> /=. apply eqb_eq in hs. rewrite -hs in ha. rewrite ha in H2.
     case: H2=> h2. rewrite -h2 in hsub. apply sub_public_always_public in hsub.
     rewrite hsub in H. 
     move: (hexpr VGamma {| scmd_sf := Istore (AA x' ei) false e :: c; rmap_sf := r1; mmap_sf := m1 |}
     {| scmd_sf := Istore (AA x' ei) false e :: c; rmap_sf := r2; mmap_sf := m2 |} e Public hr H hpub)
     => -> /=. by move: (hm x' ha)=> ->.
     move=> hx'. by move: (hm a ha).
   move=> x hx /=. by move: (hr x hx).
  (* if b i i' *)
  + move=> r1 m1 r2 m2 ov hr hm. case: b H IHhty=> //=.
    move=> bop e e' htb hrec /=.
    apply st_equiv.
    + move=> x hx /=. by move: (hr x hx).
    + move=> a ha /=. by move: (hm a ha).
    rewrite /=. inversion htb; (try discriminate); subst.
    apply union_public_always_public in H5. case: H5=> h5 h5'; subst.
    have hexpr := expr_equiv_val. have hpub : Public = Public. + by auto.
    move: (hexpr VGamma {| scmd_sf := Iif (Ebool bop e e') i i' :: c; rmap_sf := r1; mmap_sf := m1 |}
    {| scmd_sf := Iif (Ebool bop e e') i i' :: c; rmap_sf := r2; mmap_sf := m2 |} e Public hr H3 hpub)
    => -> /=. 
    by move: (hexpr VGamma {| scmd_sf := Iif (Ebool bop e e') i i' :: c; rmap_sf := r1; mmap_sf := m1 |}
    {| scmd_sf := Iif (Ebool bop e e') i i' :: c; rmap_sf := r2; mmap_sf := m2 |} e' Public hr H6 hpub)
    => -> /=.
move=> r1 m1 r2 m2 ov /= hr hm; subst. by apply st_equiv; rewrite /=.
Qed.

Lemma st_show : forall s,
{| scmd_sf := scmd_sf s; rmap_sf := rmap_sf s; mmap_sf := mmap_sf s |} = s. 
Proof.
move=> s. by case: s.
Qed.

Lemma step_to_build_state : forall s l s',
sem_instr s l s' ->
s' = (build_state_instr s
     (extract_declassify_leakages l)).
Proof.
move=> [] c r1 m1 l s' hstep.
rewrite /build_state_instr /=.
case: c hstep=> //=.
+move=> hstep. by inversion hstep; (try discriminate); subst.
move=> i c hstep. case: i hstep=> //=.
(* Iempty *)
+ move=> hstep. inversion hstep; (try discriminate); subst.
  by inversion H; (try discriminate); subst.
(* x := e *)
+ move=> x d e hstep. case: d hstep=> //=.
  + move=> hstep. inversion hstep; (try discriminate); subst.
    by case: d hstep H=> //= hstep [] h1 h2 h3; subst.
  move=> hstep. inversion hstep; (try discriminate); subst; rewrite /=.
  by case: d hstep H=> //= hstep [] h1 h2 h3; subst.
(* x := a[e] *)
+ move=> x d a hstep. case: d hstep=> //=.
  + move=> hstep. inversion hstep; (try discriminate); subst.
    by case: d hstep H=> //= hstep [] h1 h2 h3; subst.
  move=> hstep. inversion hstep; (try discriminate); subst; rewrite /=.
  by case: d hstep H=> //= hstep [] h1 h2 h3; subst.
(* a[e] := e *)
+ move=> x d e hstep. case: d hstep=> //=.
  + move=> hstep. inversion hstep; (try discriminate); subst.
    by case: d hstep H=> //= hstep [] h1 h2 h3; subst.
  move=> hstep. inversion hstep; (try discriminate); subst; rewrite /=.
  by case: d hstep H=> //= hstep [] h1 h2 h3; subst.
(* if b i i' *)
move=> b i i' hstep. case: b hstep=> //= bop e e' hstep.
inversion hstep; (try discriminate); subst.
by inversion H; (try discriminate); subst.
Qed.

Lemma preservation_without_semantic : forall VGamma AGamma s ov,
type_cmd VGamma AGamma s.(scmd_sf) ->
type_cmd VGamma AGamma (build_state_instr s ov).(scmd_sf).
Proof.
move=> VGamma AGamma [] c r m ov /= [] /=; last by constructor.
move=> {c} i c hi hc.
rewrite /build_state_instr /=.
case: hi=> //=.
+ by move=> x d [] a ei T T' htx hta hsub /=.
+ by move=> e d [] a ei T T' htx hta hsub /=.
move=> [] bop e e' {i} i i' htb hti hti' /=.
apply type_concat=> //=. by case: ifP.
Qed.

Lemma declassify_mem_to_leakages : forall VGamma AGamma c,
type_cmd VGamma AGamma c -> 
(forall s1 s2 ov, 
   c = s1.(scmd_sf) ->
   state_equiv s1 s2 VGamma AGamma ->
   build_c_leakage s1 ov = build_c_leakage s2 ov).
Proof.
move=> VGamma AGamma c hty.
move=> [] c1 r1 m1 [] c2 r2 m2 ov hc hequiv /=; subst. 
move: hequiv=> [] hr hm /= hst; subst. rewrite /= in hty.
move: c2 r1 m1 r2 m2 hm hr hty.
induction ov.
(* ov = [::] *)
+ move=> c2 r1 m1 r2 m2 hm hr hty.
  by case: c2 hm hr hty=> //=.
move=> c2 r1 m1 r2 m2 hm hr hty.
case: c2 hm hr hty=> /=.
(* empty seq of instructions *)
+ by move=> hm hr hty. 
(* i :: c *)
move=> i c hm hr /= hty; rewrite /=.
have heq : scmd_sf {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |} = i :: c. + by auto.
have heq' : i :: c = scmd_sf {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |}. + by auto.
have hequiv : state_equiv {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |}
              {| scmd_sf := i :: c; rmap_sf := r2; mmap_sf := m2 |} VGamma AGamma.
+ apply st_equiv; by auto.
have hsteq := step_declassify_state_equiv.
move: (hsteq VGamma AGamma (i::c) {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |}
{| scmd_sf := i :: c; rmap_sf := r2; mmap_sf := m2 |} a hty heq hequiv)=> hequiv'.
move: hequiv'=> [] hr' hm' hst.
have hty' := preservation_without_semantic {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |} a hty. 
move: (IHov (scmd_sf (build_state_instr {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |} a))
            (rmap_sf (build_state_instr {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |} a))
            (mmap_sf (build_state_instr {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |} a))
            (rmap_sf (build_state_instr {| scmd_sf := i :: c; rmap_sf := r2; mmap_sf := m2 |} a))
            (mmap_sf (build_state_instr {| scmd_sf := i :: c; rmap_sf := r2; mmap_sf := m2 |} a)) hm' hr' hty')=> /= {IHov} IHov.
rewrite st_show in IHov. rewrite hst st_show in IHov. rewrite IHov.
by have -> := declassify_mem_to_leakage hty a heq' hequiv.
Qed.

Lemma declassify_to_leakage_c : forall VGamma AGamma c,
type_cmd VGamma AGamma c ->
(forall s1 s1' n l, 
 c = s1.(scmd_sf) ->
 multi_step s1 l n s1' -> 
 build_c_leakage s1 (extract_declassify_leakagess l) = l).
Proof.
move=> VGamma AGamma c /= hty.
move=> [] c1 r1 m1 s1' n l hc hmulti; subst. 
move: c1 r1 m1 s1' l hmulti hty.
induction n.
(* n = 0 *)
+ move=> c1 r1 m1 s1' l hmulti hty /=.
  (* 0 step means s1 = s1' and no leakage [::] *)
  inversion hmulti; (try discriminate); subst; rewrite /=.
  + by case: c1 hmulti hty.
  by case: (n) H=> //=.
(* n != 0 *)
move=> c1 r1 m1 s1' l hmulti hty.
rewrite -addn1 in hmulti. 
inversion hmulti; (try discriminate); subst.
(* empty leakage *)
+ by case: n H2 IHn hmulti=> //=.
(* non-empty leakage *)
case: c1 hty hmulti H0=> //=.
(* empty seq of instructions *)
+ move=> hty hmulti hsem.
  inversion hmulti; (try discriminate); subst.
  by inversion H5; (try discriminate); subst.
(* i :: c *)
move=> i c hty hmulti H0 /=.
inversion hmulti; (try discriminate); subst.
apply PeanoNat.Nat.add_cancel_r in H; rewrite -H in H5.
apply PeanoNat.Nat.add_cancel_r in H5 ; subst.
have heq : i :: c = {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |}.(scmd_sf). + by auto.
have heq' : {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |}.(scmd_sf) = i :: c. + by auto.
have hnext : s'0 = build_state_instr {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |} 
                   (extract_declassify_leakages l0).
+ by have := step_to_build_state H6. 
have -> := declassify_to_leakage_i hty heq H6. rewrite heq in hty.
rewrite hnext in H8 H6. 
have hty' := preservation_without_semantic {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |} (extract_declassify_leakages l0) hty.
move: (IHn (scmd_sf (build_state_instr {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |} (extract_declassify_leakages l0)))
           (rmap_sf (build_state_instr {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |} (extract_declassify_leakages l0)))
           (mmap_sf (build_state_instr {| scmd_sf := i :: c; rmap_sf := r1; mmap_sf := m1 |} (extract_declassify_leakages l0)))
           s1' l')=> {IHn} IHn.
rewrite st_show in IHn.
by move: (IHn H8 hty')=> ->.
Qed.

Lemma deterministic_step : forall s1 l1 l2 s2 s2',
sem_instr s1 l1 s2 ->
sem_instr s1 l2 s2' ->
l1 = l2.
Proof.
move=> [] c r m l1 l2 s2 s2' hstep hstep'.
case: c hstep hstep'.
+ move=> hstep hstep'. by inversion hstep; (try discriminate); subst.
move=> i c hstep hstep'.
case: i hstep hstep'.
(* Iempty *)
+ move=> hstep hstep'. inversion hstep; (try discriminate); subst.
  by inversion hstep'; (try discriminate); subst.
(* x := e *)
+ move=> x d e hstep hstep'. inversion hstep; (try discriminate); subst.
  inversion hstep'; (try discriminate); subst.
  case: H=> h1 h2 h3 h4; subst. by case: H0=> h1' h2' h3' h4'; subst.
(* x := a[e] *)
+ move=> x d a hstep hstep'. inversion hstep; (try discriminate); subst.
  inversion hstep'; (try discriminate); subst.
  case: H=> h1 h2 h3 h4; subst. by case: H0=> h1' h2' h3' h4'; subst.
(* a[e] := e *)
+ move=> a d e hstep hstep'. inversion hstep; (try discriminate); subst.
  inversion hstep'; (try discriminate); subst.
  case: H=> h1 h2 h3 h4; subst. by case: H0=> h1' h2' h3' h4'; subst.
(* if b i i' *)
move=> b i i' hstep hstep'. inversion hstep; (try discriminate); subst.
inversion hstep'; (try discriminate); subst.
case: H=> h1 h2 h3 h4; subst. by case: H0=> h1' h2' h3' h4'; subst.
Qed.

Lemma leakage_eq_n : forall s l n s',
multi_step s l n s' ->
size l = n.
Proof.
move=> [] st r m l n [] st' r' m' hmulti.
induction hmulti; auto.
by induction H;rewrite -cat1s size_cat /= IHhmulti add1n /= addn1. 
Qed.

Lemma empty_cmd_no_leakage: forall r m l1 n1 s2,
multi_step {| scmd_sf := [::]; rmap_sf := r; mmap_sf := m |} l1 n1 s2 ->
l1 = [::].
Proof.
move=> r m l1 n1 s2 hmulti. case: s2 hmulti=> //= c' r' m' hmulti.
inversion hmulti; (try discriminate); subst=> //=.
by inversion H; (try discriminate); subst.
Qed.

Lemma type_declassify_ct_to_ct : forall VGamma AGamma s1 s2,
type_cmd VGamma AGamma s1.(scmd_sf) /\ constant_time_declassify VGamma AGamma s1 s2 ->
constant_time VGamma AGamma s1 s2.
Proof.
move=> VGamma AGamma s1 s2 hty. rewrite /constant_time /=.
case: hty=> [] hty hdeclassify. rewrite /constant_time_declassify in hdeclassify.
move=> s1' s2' l1 l2 n hequiv hmulti hmulti'.
move: (hdeclassify s1' s2' l1 l2 n hequiv hmulti hmulti')=> [] hdeq hsafe {hdeclassify}.
split; last by split=> //= hst; apply safe_lang.
move: s1 s2 l1 l2 hmulti hmulti' hequiv hty hdeq.
induction n.
(* n = 0 *)
+ move=> s1 s2 l1 l2 hmulti hmulti' hequiv hty hdeq.
  inversion hmulti; (try discriminate); subst.
  inversion hmulti'; (try discriminate); subst; auto.
  + by case:(n) H.
  by case: (n) H.
move=> s1 s2 l1 l2 hmulti hmulti' hequiv hty hdeq. 
inversion hmulti; (try discriminate); subst.
inversion hmulti'; (try discriminate); subst; auto.
have hd:= declassify_to_leakage_i. have heq : forall s, scmd_sf s = scmd_sf s. + by auto.
move: (hd VGamma AGamma (scmd_sf s1) hty s1 s' l (heq s1) H0)=> <- /=.
have hequiv' := hequiv.
case: hequiv=> [] hr hm hst. rewrite hst in hty.
move: (hd VGamma AGamma (scmd_sf s2) hty s2 s'0 l0 (heq s2) H2)=> <- /=.
case: hdeq=> hd1 hds1. rewrite hd1.
rewrite addn1 in H1. case: H1=> h1; subst.
rewrite addn1 in H. case: H=> h; subst.
have hequiv'' := step_declassify_state_equiv (extract_declassify_leakages l) hty hst hequiv'.
have hs1eq := step_to_build_state H0. rewrite -hs1eq in hequiv''.
have hs2eq := step_to_build_state H2. rewrite hd1 -hs2eq in hequiv''.
rewrite -hst in hty.
have hty' := preservation hty H0. 
move: (IHn s' s'0 l' l'0 H3 H6 hequiv'' hty' hds1)=> ->.
by have -> := declassify_mem_to_leakage hty (extract_declassify_leakages l0) (heq s1) hequiv'.
Qed.


