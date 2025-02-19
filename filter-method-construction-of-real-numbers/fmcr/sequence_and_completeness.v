(*        This file presents the formalization of sequence and          *)
(*                     completeness of real numbers.                    *)
(*   It is developmented in the CoqIDE (version 8.13.2) for windows.    *)

(** sequence_and_completeness *)

Require Export fmcr.N_Z_Q_in_R.

(* 定义 ω中的数列. *)
Definition ω_Seq f := Function f /\ dom(f) = ω /\ ran(f) ⊂ ω.

Open Scope n'_scope.

(* 定义 ω中数列f在*N中的延伸数列. *)
Definition N'_extSeq f := \{\ λ u v, u ∈ N' /\ v = f〈u〉 \}\.

Property N'_extSeq_is_Function : ∀ f, Function (N'_extSeq f)
  /\ dom(N'_extSeq f) = N'.
Proof.
  repeat split; intros.
  - unfold Relation; intros.
    apply AxiomII in H as [_[x[y[]]]]; eauto.
  - apply AxiomII' in H as [_[]].
    apply AxiomII' in H0 as [_[]]. rewrite H1,H2; auto.
  - apply AxiomI; split; intros. apply AxiomII in H as [H[]].
    apply AxiomII' in H0; tauto. apply AxiomII; split; eauto.
    exists f〈z〉. apply AxiomII'; split; auto. apply MKT49a; eauto.
    apply (MKT33 pow(ω)). apply MKT38a. pose proof MKT138. eauto.
    unfold Included; intros. apply AxiomII in H0 as [H0[]].
    apply AxiomII; auto.
Qed.

(* 此引理为证明下面的延伸数列的值域做准备. *)
Lemma N'_extSeq_ran_Lemma: ∀ f g, Function f -> Function g
  -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
  -> Function (f ∘ g) /\ dom(f ∘ g) = ω /\ ran(f ∘ g) ⊂ ω.
Proof.
  intros. assert (Function (f ∘ g)). { apply MKT64; auto. }
  split; auto. split. apply AxiomI; split; intros.
  - apply AxiomII in H6 as [H6[y]].
    apply AxiomII' in H7 as [H7[y1[]]].
    apply Property_dom in H8. rewrite <-H2; auto.
  - apply AxiomII; split; eauto. exists (f[g[z]]).
    assert (g[z] ∈ ω).
    { rewrite <-H2 in H6.
      apply Property_Value,Property_ran,H4 in H6; auto. }
    assert (f[g[z]] ∈ ω).
    { rewrite <-H1 in H7.
      apply Property_Value,Property_ran,H3 in H7; auto. }
    apply AxiomII'; split. apply MKT49a; eauto.
    exists (g[z]). rewrite <-H2 in H6.
    apply Property_Value in H6; auto. split; auto.
    rewrite <-H1 in H7. apply Property_Value in H7; auto.
  - unfold Included; intros. apply AxiomII in H6 as [H6[]].
    apply AxiomII' in H7 as [H7[y[]]].
    apply Property_ran,H3 in H9; auto.
Qed.

Property N'_extSeq_ran : ∀ f, ω_Seq f -> ran(N'_extSeq f) ⊂ N'.
Proof.
  unfold Included; intros. apply AxiomII in H0 as [H0[]].
  apply AxiomII' in H1 as [H1[]]. destruct H as [H[]].
  apply AxiomII in H2 as [H2[f1[H6[H7[]]]]].
  rewrite H9,FT10_Lemma in H3; auto. pose proof H.
  apply (N'_extSeq_ran_Lemma f f1) in H10 as [H10[]]; auto.
  apply AxiomII; split; eauto. pose proof MKT138. eauto. rewrite H4. red; auto.
Qed.

Property ω_Seq_equ_Finite_extSeq : ∀ f m, ω_Seq f -> m ∈ ω
  -> F f[m] = (N'_extSeq f)[F m].
Proof.
  intros. destruct H as [H[]]. destruct (N'_extSeq_is_Function f) as [].
  pose proof H0. rewrite <-H1 in H5. apply Property_Value,Property_ran in H5; auto.
  pose proof H0. apply (Fn_in_N' m) in H6. rewrite <-H4 in H6.
  apply Property_Value,AxiomII' in H6 as [_[]]; auto.
  rewrite H7. symmetry. apply FT5_a; auto. pose proof MKT138; eauto.
Qed.

Property N'_extSeq_Value : ∀ f n, ω_Seq f -> n ∈ N' -> (N'_extSeq f)[n] = f〈n〉.
Proof.
  intros. destruct (N'_extSeq_is_Function f). rewrite <-H2 in H0.
  apply Property_Value in H0; auto. apply AxiomII' in H0; tauto.
Qed.

(* 性质1: 序保持(两个数列的比较)

         对于两个数列 f g, 若对所有n都有 f[n] < g[n](f的每一项都小于g的每一项)
                         则对于f和g各自的延伸也满足 extf‹n› < extg‹n›

         也就是说,两个数列之间的序关系会保持到各自延伸后的数列中 *)
Property N'_extSeq_Property1: ∀ f g M, ω_Seq f -> ω_Seq g
  -> (∀ m, m ∈ ω -> f[m] ∈ g[m]) -> M ∈ N'
  -> (N'_extSeq f)[M] < (N'_extSeq g)[M].
Proof.
  intros. rewrite N'_extSeq_Value,N'_extSeq_Value; auto.
  destruct H as [H[]]. destruct H0 as [H0[]].
  apply AxiomII in H2 as [H2[h[H8[H9[]]]]].
  assert (∀ n, n ∈ ω -> f[h[n]] ∈ g[h[n]]).
  { intros. rewrite <-H9 in H11.
    apply Property_Value,Property_ran,H7 in H11; auto. }
  assert (\{ λ u, (f ∘ h)[u] ∈ (g ∘ h)[u] \} = ω ).
  { apply AxiomI; split; intros. apply AxiomII in H12 as [].
    apply (N'_extSeq_ran_Lemma f h) in H as [H[]]; auto.
    apply NNPP; intro. rewrite <-H14 in H16. apply MKT69a in H16.
    rewrite H16 in H13. elim MKT39. eauto. apply AxiomII; repeat split; eauto.
    rewrite Q'_N_propersubset_Q'_N'_Lemma,Q'_N_propersubset_Q'_N'_Lemma; auto. }
  rewrite H10,FT10_Lemma,FT10_Lemma; pose proof MKT138; eauto;
  [ |rewrite H5|rewrite H3]; unfold Included; auto. pose proof H; pose proof H0.
  apply (N'_extSeq_ran_Lemma f h) in H14 as [H14[]]; auto.
  apply (N'_extSeq_ran_Lemma g h) in H15 as [H15[]]; auto.
  apply N'_Ord_Instantiate; auto. rewrite H12. destruct NPAUF as [[_[H20 _]] _].
  apply AxiomII in H20 as [H20[[_[_[]]]]]; auto.
Qed.

(* 性质2: 单调性保持

       若数列f是单调增长的：n < m -> f[n] < f[m]
       则其相应的延伸数列也是单调增长的：N < M -> extf[N] < extg[M]     *)
Property N'_extSeq_Property2: ∀ f M N, ω_Seq f
  -> (∀ m n, m ∈ ω -> n ∈ ω -> m ∈ n -> f[m] ∈ f[n])
  -> M ∈ N' -> N ∈ N' -> M < N -> (N'_extSeq f)[M] < (N'_extSeq f)[N].
Proof.
  intros. rewrite N'_extSeq_Value,N'_extSeq_Value; auto.
  destruct H as [H[]]. apply AxiomII' in H3 as [].
  apply AxiomII in H1 as [H1[h1[H7[H8[]]]]].
  apply AxiomII in H2 as [H2[h2[H11[H12[]]]]].
  pose proof H7. apply (H6 h1 h2) in H15; auto. clear H6.
  rewrite H10,H14,FT10_Lemma,FT10_Lemma; auto; pose proof MKT138; eauto;
  try (rewrite H4; unfold Included; auto). pose proof H; pose proof H.
  apply (N'_extSeq_ran_Lemma f h1) in H16 as [H16[]]; auto.
  apply (N'_extSeq_ran_Lemma f h2) in H17 as [H17[]]; auto.
  apply N'_Ord_Instantiate; auto.
   assert (\{ λ w, h1[w] ∈ h2[w] \} ⊂ \{ λ w, (f ∘ h1)[w] ∈ (f ∘ h2)[w] \}).
  { unfold Included; intros. apply AxiomII in H22 as [].
    assert (z ∈ ω).
    { apply NNPP; intro. rewrite <-H8 in H24. apply MKT69a in H24.
      rewrite H24 in H23. elim MKT39. eauto. } apply AxiomII; split; eauto.
    rewrite Q'_N_propersubset_Q'_N'_Lemma,Q'_N_propersubset_Q'_N'_Lemma; auto.
    apply H0; auto; [apply H9|apply H13];
    apply (@ Property_ran z),Property_Value; auto;
    [rewrite H8|rewrite H12]; auto. } destruct NPAUF as [[_[H23 _]]_].
  apply AxiomII in H23 as [_[[_[_[_[]]]]]].
  apply (H24 (\{ λ w, h1[w] ∈ h2[w] \})); repeat split; auto.
  unfold Included; intros. apply AxiomII in H26 as [].
  apply NNPP; intro. rewrite <-H18 in H28. apply MKT69a in H28.
  rewrite H28 in H27. elim MKT39; eauto.
Qed.

(* 性质3: 数列值的一致性, 有限部分没有出现过的数, 延伸数列中也不会出现.
          对于数列: f[n] 若对于任意n和某一任意m, 都有f[n] <> m,
          则其相应的延伸数列 extg[N] 也有 extg[N] <> F m.        *)
Property N'_extSeq_Property3: ∀ f N m, ω_Seq f -> (∀ n, f[n] <> m)
  -> (N'_extSeq f)[N] <> F m.
Proof.
  destruct NPAUF as [H _]. intros. intro. assert (Ensemble (F m)).
  { destruct (classic (m ∈ ω)). apply Fn_in_N' in H3; eauto.
    apply Fa_P1 in H3. pose proof in_ω_0. rewrite H3; eauto. }
  assert (N ∈ dom(N'_extSeq f)).
  { apply NNPP; intro. apply MKT69a in H4. rewrite <-H2,H4 in H3.
    elim MKT39; auto. }
  destruct (N'_extSeq_is_Function f). pose proof H0.
  apply (N'_extSeq_ran f) in H7; auto.
  assert (m ∈ ω).
  { apply NNPP; intro. apply Fa_P1 in H8.
    apply Property_Value,Property_ran,H7 in H4; auto.
    rewrite H2,H8 in H4. apply AxiomII in H4 as [_[f1[H4[H9[]]]]].
    pose proof H4. apply (FT4 F0 f1 ω ω) in H12; auto;
    [ |pose proof MKT138; eauto]. rewrite <-H11 in H12.
    apply AxiomII in H12 as [_[[_[_[]]]]]. elim (@ MKT16 ω); auto. }
  assert (ω <> 0) as HH.
  { intro. pose proof in_ω_0. rewrite H9 in H10. elim (@ MKT16 0); auto. }
  assert (Ensemble m); eauto. apply (Const_is_Function ω) in H9 as [H9[]]; auto.
  assert (ran(Const m) ⊂ ω).
  { rewrite H11. intros z H12. apply MKT41 in H12; eauto. rewrite H12; auto. }
  pose proof H4. rewrite H6 in H13. apply AxiomII in H13 as [_[f1[H13[H14[]]]]].
  pose proof H4. apply Property_Value in H17; auto.
  apply AxiomII' in H17 as [_[_ ]]. rewrite H17 in H2. pose proof H.
  apply (FT10 _ f1 ω ω) in H18; auto. rewrite <-H16 in H18.
  assert (∀ n, n ∈ ω -> (Const m)[n] = m).
  { intros. rewrite <-H10 in H19. apply Property_Value in H19; auto.
    apply AxiomII' in H19; tauto. }
  assert ((Const m)〈N〉 = F m).
  { apply (FT6_a _ _ ω ω m); auto. destruct H18; tauto. }
  rewrite <-H20 in H2. destruct H0 as [H0[]].
  assert (AlmostEqual f (Const m) ω ω N). { destruct H18. apply H23 in H2; auto. }
  destruct H23 as [_[_[_[_[_[_[]]]]]]].
  assert (\{ λ u, u ∈ ω /\ f[u] = (Const m)[u] \} <> Φ).
  { intro. rewrite H25 in H24. apply AxiomII in H23 as [_[[_[]]]]; auto. }
  apply NEexE in H25 as [x]. apply AxiomII in H25 as [_[]].
  rewrite H19 in H26; auto. elim (H1 x); auto. pose proof MKT138; eauto.
  intro. unfold Finite in H19. rewrite Inf_P1 in H19. elim (MKT101 ω); auto.
Qed.

(* 性质4: '分数列'的单调性保持

         对于分数列:
          f[n]                                   extf[N]
          ————    若该分数列单调增, 则其相应的延伸数列 ——————  也单调增
          g[n]                                   extg[N]

        [注: 这里并不是真正意义上的分数, *N中没有'分数'的概念.
             f[m]       f[n]
             ————  前于  ————   是指:  f[m] * g[n]  前于  f[n] * g[m]
             g[m]       g[n]                                             *)
Property N'_extSeq_Property4: ∀ f g M N, ω_Seq f -> ω_Seq g
  -> (∀ m n, m ∈ ω -> n ∈ ω ->  m ∈ n -> (f[m] · g[n])%ω ∈ (f[n] · g[m])%ω)
  -> M ∈ N' -> N ∈ N' -> (M < N)%n'
  -> (N'_extSeq f)[M] · (N'_extSeq g)[N] < (N'_extSeq f)[N] · (N'_extSeq g)[M].
Proof.
  destruct NPAUF as [H _]. intros. rewrite N'_extSeq_Value,N'_extSeq_Value,
  N'_extSeq_Value,N'_extSeq_Value; auto.
  destruct H0 as [H0[]]. destruct H1 as [H1[]].
  apply AxiomII in H3 as [H3[h1[H10[H11[]]]]].
  apply AxiomII in H4 as [H4[h2[H14[H15[]]]]]. pose proof H as [_[H18 _]].
  rewrite H13,H17,FT10_Lemma,FT10_Lemma,FT10_Lemma,FT10_Lemma; auto;
  try (pose proof MKT138; eauto); try rewrite H6; try rewrite H8;
  unfold Included; auto. clear H19.
  pose proof H0; pose proof H0; pose proof H1; pose proof H1.
  apply (N'_extSeq_ran_Lemma f h1) in H19 as [H19[]];
  apply (N'_extSeq_ran_Lemma g h2) in H21 as [H21[]];
  apply (N'_extSeq_ran_Lemma f h2) in H20 as [H20[]];
  apply (N'_extSeq_ran_Lemma g h1) in H22 as [H22[]]; auto.
  rewrite N'_Mult_Instantiate,N'_Mult_Instantiate; auto.
  pose proof H21; pose proof H22.
  apply (ωFun_Mult_P1 (f ∘ h1)) in H31 as [H31[]]; auto.
  apply (ωFun_Mult_P1 (f ∘ h2)) in H32 as [H32[]]; auto.
  apply N'_Ord_Instantiate; auto. apply AxiomII' in H5 as [].
  pose proof H10. apply (H37 h1 h2) in H38; auto. clear H37.
  set (A := \{ λ w, h1[w] ∈ h2[w] \}).
  set (B := (\{ λ w, ((f ∘ h1) · (g ∘ h2))[w] ∈ ((f ∘ h2) · (g ∘ h1))[w] \})%ωfun).
  assert (A ⊂ B).
  { unfold Included; intros. apply AxiomII in H37 as []. apply AxiomII; split; auto.
    assert (z ∈ ω).
    { apply NNPP; intro. rewrite <-H11 in H40.
      apply MKT69a in H40. rewrite H40 in H39. elim MKT39; eauto. }
    rewrite ωFun_Mult_P2,Q'_N_propersubset_Q'_N'_Lemma,
    Q'_N_propersubset_Q'_N'_Lemma,ωFun_Mult_P2,Q'_N_propersubset_Q'_N'_Lemma,
    Q'_N_propersubset_Q'_N'_Lemma; auto.
    assert (h1[z] ∈ ω /\ h2[z] ∈ ω) as [].
    { split; [apply H12|apply H16]; apply (@ Property_ran z),
      Property_Value; auto; [rewrite H11|rewrite H15]; auto. }
    apply H2; auto. }
  apply AxiomII in H18 as [_[[_[_[_[]]]]]].
  apply (H39 A); repeat split; auto. unfold Included; intros.
  apply AxiomII in H41 as []. apply NNPP; intro. rewrite <-H33 in H43.
  apply MKT69a in H43. rewrite H43 in H42. elim MKT39; eauto.
Qed.

Open Scope q'_scope.

(* 定义 *Q中的自然数列. *)
Definition Q'_NatSeq f := Function f /\ dom(f) = ω /\ ran(f) ⊂ Q'_N.

(* *Q_N中自然数列 与 ω中数列 的关系 *)
Property Q'_NatSeq_and_ω_Seq : ∀ f, Q'_NatSeq f -> ω_Seq ((φ4⁻¹) ∘ f).
Proof.
  intros f [H[]]. destruct φ4_is_Function as [[][]].
  assert (Function (φ4⁻¹ ∘ f)). { apply MKT64; auto. }
  split; auto. split.
  - apply AxiomI; split; intros.
    + apply AxiomII in H7 as [H7[y]].
      apply AxiomII' in H8 as [H8[x[]]].
      apply Property_dom in H9. rewrite H0 in H9; auto.
    + apply AxiomII; split; eauto. pose proof H7.
      rewrite <-H0 in H8. apply Property_Value in H8; auto.
      pose proof H8. apply Property_ran,H1 in H9.
      replace Q'_N with ran(φ4) in H9; auto.
      rewrite reqdi in H9. apply Property_Value in H9; auto.
      pose proof H9. apply Property_ran in H10.
      exists ((φ4⁻¹)[f[z]]). apply AxiomII'; split; eauto. apply MKT49a; eauto.
  - unfold Included; intros. apply AxiomII in H7 as [H7[]].
    apply AxiomII' in H8 as [H8[y[]]]. apply Property_ran in H10.
    rewrite <-deqri,H4 in H10; auto.
Qed.

(* 定义 *Q中自然数列的延伸数列. *)
Definition Q'_extNatSeq f := φ3 ∘ (N'_extSeq ((φ4⁻¹) ∘ f)).

(* *Q中自然数列的延伸数列是*N 到 *Q_*N 的函数. *)
Property Q'_extNatSeq_is_Function : ∀ f, Q'_NatSeq f
  -> Function (Q'_extNatSeq f) /\ dom(Q'_extNatSeq f) = N'
    /\ ran(Q'_extNatSeq f) ⊂ Q'_N'.
Proof.
  intros. pose proof H. apply Q'_NatSeq_and_ω_Seq in H0; auto.
  destruct (N'_extSeq_is_Function ((φ4⁻¹) ∘ f)).
  pose proof H0. apply N'_extSeq_ran in H3; auto.
  destruct φ3_is_Function as [[][]].
  assert (Function (Q'_extNatSeq f)). { apply MKT64; auto. }
  split; auto. split; [(apply AxiomI; split)|unfold Included]; intros.
  - apply AxiomII in H9 as [H9[]]. apply AxiomII' in H10 as [H10[y[]]].
    apply Property_dom in H11. rewrite <-H2; auto.
  - pose proof H9. rewrite <-H2 in H10. apply Property_Value in H10; auto.
    pose proof H10. apply Property_ran,H3 in H11. rewrite <-H6 in H11.
    apply Property_Value in H11; auto. pose proof H11. apply Property_ran in H12.
    apply AxiomII; split; eauto. exists (φ3[(N'_extSeq ((φ4⁻¹) ∘ f))[z]]).
    apply AxiomII'; split; eauto. apply MKT49a; eauto.
  - apply AxiomII in H9 as [H9[]]. apply AxiomII' in H10 as [H10[y[]]].
    apply Property_ran in H12. rewrite φ3_ran in H12; auto.
Qed.

(* *Q中的自然数列的每一项 等于 其延伸的有限部分的每一项. *)
Property Q'_NatSeq_equ_Finite_extNatSeq :
  ∀ f m, Q'_NatSeq f -> m ∈ ω -> f[m] = (Q'_extNatSeq f)[F m].
Proof.
  intros. destruct φ3_is_Function as [[][]].
  pose proof H. apply Q'_NatSeq_and_ω_Seq in H5 as [H5[]]; auto.
  pose proof H. apply Q'_extNatSeq_is_Function in H8 as [H8[]]; auto.
  destruct (N'_extSeq_is_Function ((φ4⁻¹) ∘ f)) as [].
  assert ((F m) ∈ N'_N). { apply Fn_in_N'_N; auto. }
  pose proof H13. apply N'_N_subset_N' in H13; auto.
  unfold Q'_extNatSeq. rewrite Q'_N_propersubset_Q'_N'_Lemma,
  N'_extSeq_Value,FT5_a; auto; try split; auto. destruct φ4_is_Function as [[][]].
  destruct φ_is_Function as [[][]]. destruct H as [H[]].
  replace (F ((φ4⁻¹) ∘ f)[m]) with (φ[((φ4⁻¹) ∘ f)[m]]).
  rewrite Q'_N_propersubset_Q'_N'_Lemma,<-Q'_N_propersubset_Q'_N'_Lemma; auto.
  unfold φ3. rewrite MKT58. replace (φ2 ∘ (φ1 ∘ φ)) with φ4; auto.
  rewrite f11vi; auto. rewrite <-H23 in H0.
  apply Property_Value,Property_ran in H0; auto. rewrite <-H6 in H0.
  apply Property_Value,Property_ran,H7 in H0; auto. rewrite <-H21 in H0.
  apply Property_Value in H0; auto. apply AxiomII' in H0; tauto.
  pose proof MKT138; eauto.
Qed.

(* *Q中自然数列及其延伸的相关性质. *)
(* 性质1: 序保持(两个数列的比较)

        对于两个数列 f g, 若对所有n都有 f[n] < g[n](f的每一项都小于g的每一项)
                        则对于f和g各自的延伸也满足 extf‹n› < extg‹n›

        也就是说,两个数列之间的序关系会保持到各自延伸后的数列中 *)
Property Q'_extNatSeq_Property1 : ∀ f g M, Q'_NatSeq f -> Q'_NatSeq g
  -> (∀ m, m ∈ ω -> f[m] < g[m]) -> M ∈ N'
  -> (Q'_extNatSeq f)[M] < (Q'_extNatSeq g)[M].
Proof.
  intros. pose proof H; pose proof H0.
  apply Q'_NatSeq_and_ω_Seq in H3; apply Q'_NatSeq_and_ω_Seq in H4; auto.
  destruct φ4_is_Function as [[][]]. destruct φ3_is_Function as [[][]].
  destruct φ_is_Function as [[][]].
  assert (∀ n, n ∈ ω -> ((φ4⁻¹) ∘ f)[n] ∈ ((φ4⁻¹) ∘ g)[n]).
  { intros. rewrite Q'_N_propersubset_Q'_N'_Lemma,
    Q'_N_propersubset_Q'_N'_Lemma; auto; [ |destruct H0|destruct H]; auto.
    assert (f[n] ∈ ran(φ4) /\ g[n] ∈ ran(φ4)) as [].
    { destruct H as [H[]]. destruct H0 as [H0[]].
      split; [apply H19|apply H21]; apply (@ Property_ran n),
      Property_Value; [|rewrite H18| |rewrite H20]; auto. }
    apply (φ4_PrOrder (φ4⁻¹)[f[n]] (φ4⁻¹)[g[n]]); try rewrite <-H7,deqri;
    [apply (@ Property_ran f[n])|apply (@ Property_ran g[n])| ];
    try apply Property_Value; try rewrite <-reqdi; auto.
    rewrite f11vi,f11vi; auto. }
  apply (N'_extSeq_Property1 _ _ M) in H17; auto.
  destruct (N'_extSeq_is_Function ((φ4⁻¹) ∘ g)).
  destruct (N'_extSeq_is_Function ((φ4⁻¹) ∘ f)).
  pose proof H3; pose proof H4.
  apply N'_extSeq_ran in H22; apply N'_extSeq_ran in H23; auto.
  apply φ3_PrOrder in H17; auto; [ |apply H22|apply H23];
  try apply (@ Property_ran M),Property_Value; auto;
  [ |rewrite H21|rewrite H19]; auto. unfold Q'_extNatSeq.
  rewrite Q'_N_propersubset_Q'_N'_Lemma,Q'_N_propersubset_Q'_N'_Lemma; auto.
Qed.

(* 性质2: 单调性保持

       若数列f是单调增长的：n < m -> f[n] < f[m]
       则其相应的延伸数列也是单调增长的：N < M -> extf[N] < extg[M]  *)
Property Q'_extNatSeq_Property2 : ∀ f M N, Q'_NatSeq f
  -> (∀ m n, m ∈ ω -> n ∈ ω -> m ∈ n -> f[m] < f[n])
  -> M ∈ N' -> N ∈ N' -> (M < N)%n'
  -> (Q'_extNatSeq f)[M] < (Q'_extNatSeq f)[N].
Proof.
  intros. pose proof H. apply Q'_NatSeq_and_ω_Seq in H4; auto.
  destruct φ4_is_Function as [[][]]. destruct φ3_is_Function as [[][]].
  destruct φ_is_Function as [[][]].
  assert (∀ m n, m ∈ ω -> n ∈ ω -> m ∈ n -> ((φ4⁻¹) ∘ f)[m] ∈ ((φ4⁻¹) ∘ f)[n]).
  { intros. rewrite Q'_N_propersubset_Q'_N'_Lemma,
    Q'_N_propersubset_Q'_N'_Lemma; auto; [ |destruct H|destruct H]; auto.
    assert (f[m] ∈ ran(φ4) /\ f[n] ∈ ran(φ4)) as [].
    { destruct H as [H[]]. split; apply H21;
      [apply (@ Property_ran m)|apply (@ Property_ran n)];
      apply Property_Value; auto; rewrite H20; auto. }
    apply (φ4_PrOrder (φ4⁻¹)[f[m]] (φ4⁻¹)[f[n]]); try rewrite <-H7,deqri;
    [apply (@ Property_ran f[m])|apply (@ Property_ran f[n])| ];
    try apply Property_Value; try rewrite <-reqdi; auto.
    rewrite f11vi,f11vi; auto. }
  apply (N'_extSeq_Property2 _ M N) in H17; auto.
  destruct (N'_extSeq_is_Function ((φ4⁻¹) ∘ f)). pose proof H4.
  apply N'_extSeq_ran in H20; auto. apply φ3_PrOrder in H17; auto;
  try apply H20; [ |apply (@ Property_ran M)|apply (@ Property_ran N)];
  try (apply Property_Value; auto; rewrite H19); auto. unfold Q'_extNatSeq.
  rewrite Q'_N_propersubset_Q'_N'_Lemma,Q'_N_propersubset_Q'_N'_Lemma; auto.
Qed.

(* 性质3: 数列值的一致性.

         有限部分没有出现过的数, 延伸数列中也不会出现.
         对于数列: f[n] 若对于任意n和某一任意m, 都有f[n] <> m,
         则其相应的延伸数列 extg[N] 也有 extg[N] <> m *)
Property Q'_extNatSeq_Property3 : ∀ f N m, Q'_NatSeq f -> m ∈ Q'_N
  -> (∀ n, f[n] <> m) -> (Q'_extNatSeq f)[N] <> m.
Proof.
  intros. intro. pose proof H. apply Q'_NatSeq_and_ω_Seq in H3; auto.
  destruct φ4_is_Function as [[][]]. destruct φ3_is_Function as [[][]].
  destruct φ_is_Function as [[][]]. destruct (N'_extSeq_is_Function ((φ4⁻¹) ∘ f)).
  pose proof H3. apply (N'_extSeq_ran ((φ4⁻¹) ∘ f)) in H18.
  pose proof H. apply (Q'_extNatSeq_is_Function f) in H19 as [H19[]]; auto.
  assert (φ3[F ((φ4⁻¹)[m])] = m) as Ha.
  { pose proof H0. unfold Q'_N in H22. rewrite reqdi in H22.
    apply Property_Value,Property_ran in H22; auto.
    rewrite <-deqri,H6 in H22. rewrite <-H14 in H22.
    apply Property_Value,AxiomII' in H22 as [_[]]; auto.
    rewrite <-φ3_Lemma,<-H23,φ4_Lemma,f11vi; auto. apply Fn_in_N'; auto. }
  assert (∀ n, ((φ4⁻¹) ∘ f)[n] <> (φ4⁻¹)[m]).
  { intros. intro. assert (φ4[((φ4⁻¹) ∘ f)[n]] = φ4[(φ4⁻¹)[m]]).
    { rewrite H22; auto. } destruct H as [H[]]. destruct (classic (n ∈ dom(f))).
    - rewrite f11vi,Q'_N_propersubset_Q'_N'_Lemma,f11vi in H23; auto.
      elim (H1 n); auto. apply Property_Value,Property_ran in H26; auto.
    - unfold Q'_N in H0. rewrite reqdi in H0. apply Property_Value,
      Property_ran in H0; auto. apply MKT69a in H26.
      rewrite Q'_N_propersubset_Q'_N'_Lemma in H22; auto.
      assert (~ μ ∈ dom(φ4⁻¹)). { intro. elim MKT39; eauto. }
      apply MKT69a in H27. rewrite <-H22,H26,H27 in H0. elim MKT39; eauto. }
  apply (N'_extSeq_Property3 _ N) in H22; auto. unfold Q'_N in H0.
  rewrite reqdi in H0. apply Property_Value,Property_ran in H0; auto.
  rewrite <-deqri,H6 in H0. apply Fn_in_N'_N,N'_N_subset_N' in H0; auto.
  destruct (classic (N ∈ N')).
  - unfold Q'_extNatSeq in H2. rewrite Q'_N_propersubset_Q'_N'_Lemma in H2; auto.
    assert ((φ3⁻¹)[φ3[(N'_extSeq ((φ4⁻¹) ∘ f))[N]]] = (φ3⁻¹)[φ3[F (φ4⁻¹)[m]]]).
    { rewrite H2,Ha; auto. }
    rewrite f11iv,f11iv in H24; try rewrite H10; auto.
    apply H18,(@ Property_ran N),Property_Value; auto. rewrite H17; auto.
  - rewrite <-H20 in H23. apply MKT69a in H23. rewrite <-H10 in H0.
    apply Property_Value,Property_ran in H0; auto.
    rewrite Ha,<-H2,H23 in H0. elim MKT39; eauto.
Qed.

(* 性质4: '分数列'的单调性保持

         对于分数列:
          f[n]                                   extf[N]
          ————    若该分数列单调增, 则其相应的延伸数列 ——————  也单调增
          g[n]                                   extg[N]

        [注: 这里分数用除法表示.]       *)
Property Q'_extNatSeq_Property4 : ∀ f g M N, Q'_NatSeq f -> Q'_NatSeq g
  -> (∀ n, g[n] <> Q'0)
  -> (∀ m n, m ∈ ω -> n ∈ ω -> m ∈ n -> (f[m] / g[m]) < (f[n] / g[n]))
  -> M ∈ N' -> N ∈ N' -> (M < N)%n'
  -> (Q'_extNatSeq f)[M] / (Q'_extNatSeq g)[M]
    < (Q'_extNatSeq f)[N] / (Q'_extNatSeq g)[N].
Proof.
  intros. pose proof H; pose proof H0.
  apply Q'_NatSeq_and_ω_Seq in H6; apply Q'_NatSeq_and_ω_Seq in H7; auto.
  destruct φ4_is_Function as [[][]]. destruct φ3_is_Function as [[][]].
  destruct φ_is_Function as [[][]].
  destruct (N'_extSeq_is_Function ((φ4⁻¹) ∘ f)).
  destruct (N'_extSeq_is_Function ((φ4⁻¹) ∘ g)).
  pose proof H6; pose proof H7.
  apply (N'_extSeq_ran ((φ4⁻¹) ∘ f)) in H24;
  apply (N'_extSeq_ran ((φ4⁻¹) ∘ g)) in H25; auto.
  pose proof H; pose proof H0.
  apply (Q'_extNatSeq_is_Function f) in H26 as [H26[]];
  apply (Q'_extNatSeq_is_Function g) in H27 as [H27[]]; auto.
  assert (∀ M, (Q'_extNatSeq g)[M] <> Q'0).
  { intros. apply Q'_extNatSeq_Property3; auto. apply Q'0_in_Q'_N; auto. }
  assert ((N'_extSeq ((φ4⁻¹) ∘ f))[N] ∈ N'
    /\ (N'_extSeq ((φ4⁻¹) ∘ g))[M] ∈ N'
    /\ (N'_extSeq ((φ4⁻¹) ∘ f))[M] ∈ N'
    /\ (N'_extSeq ((φ4⁻¹) ∘ g))[N] ∈ N') as [H33[H34[]]].
  { repeat split;
    [apply H24,(@ Property_ran N)|apply H25,(@ Property_ran M)|
     apply H24,(@ Property_ran M)|apply H25,(@ Property_ran N)];
    apply Property_Value; try rewrite H21; try rewrite H23; auto. }
  assert ((Q'_extNatSeq f)[M] · (Q'_extNatSeq g)[N]
    < (Q'_extNatSeq f)[N] · (Q'_extNatSeq g)[M]).
  { unfold Q'_extNatSeq. rewrite Q'_N_propersubset_Q'_N'_Lemma,
    Q'_N_propersubset_Q'_N'_Lemma,Q'_N_propersubset_Q'_N'_Lemma,
    Q'_N_propersubset_Q'_N'_Lemma; auto.
    rewrite <-φ3_PrMult,<-φ3_PrMult; auto.
    apply φ3_PrOrder; try apply N'_Mult_in_N'; auto.
    apply N'_extSeq_Property4; auto. intros. pose proof H39.
    apply H2 in H40; auto. rewrite Q'_N_propersubset_Q'_N'_Lemma,
    Q'_N_propersubset_Q'_N'_Lemma,Q'_N_propersubset_Q'_N'_Lemma,
    Q'_N_propersubset_Q'_N'_Lemma; auto;
    [ |destruct H0|destruct H|destruct H0|destruct H]; auto.
    assert (f[m] ∈ Q'_N /\ g[n] ∈ Q'_N
      /\ f[n] ∈ Q'_N /\ g[m] ∈ Q'_N) as [H41[H42[]]].
    { destruct H as [H[]]. destruct H0 as [H0[]]. repeat split;
      [apply H42,(@ Property_ran m)|apply H44,(@ Property_ran n)|
       apply H42,(@ Property_ran n)|apply H44,(@ Property_ran m)];
      apply Property_Value; try rewrite H41; try rewrite H43; auto. }
    assert ((φ4⁻¹)[f[n]] ∈ ω /\ (φ4⁻¹)[g[m]] ∈ ω
      /\ (φ4⁻¹)[f[m]] ∈ ω /\ (φ4⁻¹)[g[n]] ∈ ω) as [H45[H46[]]].
    { repeat split; rewrite <-H10,deqri;
      [apply (@ Property_ran f[n])|apply (@ Property_ran g[m])|
       apply (@ Property_ran f[m])|apply (@ Property_ran g[n])];
      try apply Property_Value; try rewrite <-reqdi; auto. }
    apply φ4_PrOrder; try apply ω_Mult_in_ω; auto.
    rewrite φ4_PrMult,φ4_PrMult,f11vi,f11vi,f11vi,f11vi; auto.
    assert (Q'0 < g[m] /\ Q'0 < g[n]) as [].
    { pose proof Q'0_in_Q'. split; apply Q'_N_Q'0_is_FirstMember;
      try (apply MKT4'; split); auto; apply AxiomII; split; eauto;
      intro; apply MKT41 in H50; eauto; [elim (H1 m)|elim (H1 n)]; auto. }
    apply Q'_N_subset_Q' in H41,H42,H43,H44; auto.
    assert (g[m] <> Q'0 /\ g[n] <> Q'0) as [].
    { split; intro; [rewrite H51 in H49|rewrite H51 in H50];
      elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
    apply (Q'_Mult_PrOrder _ _ g[m]) in H40; auto with Q'.
    rewrite Q'_Divide_Property3 in H40; auto.
    apply (Q'_Mult_PrOrder _ _ g[n]) in H40; auto with Q'.
    rewrite <-Q'_Mult_Association,(Q'_Mult_Commutation _ g[m]),
    Q'_Mult_Association,Q'_Divide_Property3,Q'_Mult_Commutation,
    (Q'_Mult_Commutation g[m]) in H40; auto with Q'. }
  assert ((Q'_extNatSeq f)[M] ∈ Q'_N' /\ (Q'_extNatSeq g)[N] ∈ Q'_N'
    /\ (Q'_extNatSeq f)[N] ∈ Q'_N' /\ (Q'_extNatSeq g)[M] ∈ Q'_N') as [H38[H39[]]].
  { repeat split;
    [apply H29,(@ Property_ran M)|apply H31,(@ Property_ran N)|
     apply H29,(@ Property_ran N)|apply H31,(@ Property_ran M)];
    apply Property_Value; try rewrite H28; try rewrite H30; auto. }
  pose proof H39; pose proof H41.
  apply Q'_N'_propersubset_Q'_Z',Q'_Z'_propersubset_Q' in H38; auto.
  apply Q'_N'_propersubset_Q'_Z',Q'_Z'_propersubset_Q' in H39; auto.
  apply Q'_N'_propersubset_Q'_Z',Q'_Z'_propersubset_Q' in H40; auto.
  apply Q'_N'_propersubset_Q'_Z',Q'_Z'_propersubset_Q' in H41; auto.
  apply Q'_N'_Q'0_is_FirstMember in H42; auto.
  apply Q'_N'_Q'0_is_FirstMember in H43; auto.
  assert ((Q'_extNatSeq g)[M] <> Q'0 /\ (Q'_extNatSeq g)[N] <> Q'0) as [].
  { split; intro; [rewrite H44 in H43|rewrite H44 in H42];
    elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
  apply (Q'_Mult_PrOrder _ _ (Q'_extNatSeq g)[M]); auto with Q'.
  rewrite Q'_Divide_Property3; auto.
  apply (Q'_Mult_PrOrder _ _ (Q'_extNatSeq g)[N]); auto with Q'.
  rewrite <-Q'_Mult_Association,(Q'_Mult_Commutation _ (Q'_extNatSeq g)[M]),
  Q'_Mult_Association,Q'_Divide_Property3,Q'_Mult_Commutation,
  (Q'_Mult_Commutation (Q'_extNatSeq g)[M]); auto with Q'.
Qed.

(* *Q_N 的原像集是 *N_N *)
Lemma Q'_N_PreimageSet_N'_N : (φ3)⁻¹「Q'_N」 = N'_N.
Proof.
  intros. destruct φ3_is_Function as [[][]]. destruct φ4_is_Function as [[][]].
  destruct φ_is_Function as [[][]]. apply AxiomI; split; intros.
  - apply AxiomII in H11 as [H11[]]. unfold Q'_N in H13.
    pose proof H13. rewrite reqdi in H14.
    apply Property_Value,Property_ran in H14; auto.
    rewrite <-deqri in H14. pose proof H14.
    rewrite H5 in H14. rewrite H5,<-H9 in H15.
    apply Property_Value,Property_ran in H15; auto.
    unfold φ4 in H15. rewrite MKT62,MKT62,MKT58,<-MKT62 in H15.
    replace ((φ2 ∘ φ1)⁻¹) with (φ3⁻¹) in H15; auto.
    rewrite Q'_N_propersubset_Q'_N'_Lemma,f11iv in H15; auto.
    apply NNPP; intro. rewrite <-H10,reqdi in H16.
    apply MKT69a in H16. assert ((φ⁻¹)[z] ∉ dom(φ)).
    { intro. rewrite H16 in H17. elim MKT39; eauto. }
    apply MKT69a in H17. rewrite H17 in H15. elim MKT39. eauto.
  - apply AxiomII; split; eauto. split. rewrite H1.
    apply N'_N_subset_N'; auto. pose proof H11. rewrite <-H10,reqdi in H12.
    apply Property_Value,Property_ran in H12; auto.
    rewrite <-deqri,H9 in H12. pose proof H12. rewrite <-H5 in H13.
    apply Property_Value,Property_ran in H13; auto.
    rewrite <-φ4_Lemma,f11vi,φ3_Lemma in H13; auto.
    apply N'_N_subset_N'; auto. rewrite H10; auto.
Qed.

(* 如果自然数列有一个每项固定的系数b, 那么此系数会保持到延伸数列中 *)
Lemma Q'_extNatSeq_Property5_Lemma : ∀ f g b N, Q'_NatSeq f -> Q'_NatSeq g
  -> f = \{\ λ u v, u ∈ ω /\ v = b · g[u] \}\ -> b ∈ Q'_N -> N ∈ N'
  -> (Q'_extNatSeq f)[N] = b · (Q'_extNatSeq g)[N].
Proof.
  intros. assert (∀ n, n ∈ ω -> g[n] ∈ Q'_N).
  { intros. destruct H0 as [H0[]]. rewrite <-H5 in H4.
    apply Property_Value,Property_ran,H6 in H4; auto. }
  pose proof H. apply Q'_NatSeq_and_ω_Seq in H5; auto.
  pose proof H0. apply Q'_NatSeq_and_ω_Seq in H6; auto.
  destruct φ3_is_Function as [[][]]. pose proof φ3_ran.
  destruct φ4_is_Function as [[][]]. destruct φ_is_Function as [[][]].
  destruct (N'_extSeq_is_Function ((φ4⁻¹) ∘ f)).
  pose proof H5. apply (N'_extSeq_ran ((φ4⁻¹) ∘ f)) in H22; auto.
  destruct (N'_extSeq_is_Function ((φ4⁻¹) ∘ g)).
  pose proof H6. apply (N'_extSeq_ran ((φ4⁻¹) ∘ g)) in H25; auto.
  unfold Q'_extNatSeq. rewrite Q'_N_propersubset_Q'_N'_Lemma,
  Q'_N_propersubset_Q'_N'_Lemma; auto.
  assert (b = φ3[φ3⁻¹[b]]).
  { rewrite f11vi; auto. rewrite H11. apply Q'_N_propersubset_Q'_N'; auto. }
  rewrite H26,<-φ3_PrMult; [ |rewrite <-H9,deqri|apply H25];
  try (apply (@ Property_ran N),Property_Value);
  try (apply (@ Property_ran b),Property_Value);
  try rewrite <-reqdi,H11; try rewrite H24; auto;
  [ |apply Q'_N_propersubset_Q'_N']; auto.
  assert ((φ4⁻¹)[b] ∈ ω).
  { rewrite <-H14,deqri. apply (@ Property_ran b),Property_Value; auto.
    rewrite <-reqdi; auto. }
  assert ((φ3⁻¹)[b] = F ((φ4⁻¹)[b])).
  { rewrite <-H18 in H27. apply Property_Value in H27; auto.
    apply AxiomII' in H27 as [_[]]. rewrite <-H28. unfold φ4.
    rewrite MKT62,MKT62,MKT58,<-MKT62.
    rewrite Q'_N_propersubset_Q'_N'_Lemma,f11vi; auto.
    unfold φ4 in H28. rewrite H19,<-Q'_N_PreimageSet_N'_N;auto.
    pose proof H2. apply Q'_N_propersubset_Q'_N' in H29; auto.
    rewrite <-H11 in H29. pose proof H29. rewrite reqdi in H30.
    apply Property_Value,Property_ran in H30; auto.
    rewrite <-deqri in H30. apply AxiomII; repeat split; eauto.
    rewrite f11vi; auto. }
  assert (ω <> 0) as HH.
  { intro. pose proof in_ω_0. rewrite H29 in H30. elim (@ MKT16 0); auto. }
  assert ((N'_extSeq (φ4⁻¹ ∘ f))[N] = (φ3⁻¹)[b] · (N'_extSeq ((φ4⁻¹) ∘ g))[N])%n'.
  { rewrite N'_extSeq_Value,N'_extSeq_Value; auto. pose proof H27.
    apply Fn_in_N'_N,N'_N_subset_N' in H29; auto.
    assert (Ensemble ((φ4⁻¹) [b])); eauto.
    apply (Const_is_Function ω) in H30 as [H30[]]; auto.
    assert (ran(Const (φ4⁻¹)[b]) ⊂ ω).
    { unfold Included; intros. rewrite H32 in H33.
      apply MKT41 in H33; eauto. rewrite H33; auto. }
    assert (∀ n, n ∈ ω -> (Const (φ4⁻¹)[b])[n] = (φ4⁻¹)[b]).
    { intros. rewrite <-H31 in H34. apply Property_Value in H34; auto.
      apply AxiomII' in H34; tauto. }
    pose proof H27. apply (F_Const_Fa F0 ω) in H35;
    [ |destruct NPAUF as [[_[]]_]]; auto.
    apply AxiomII in H3 as [H3[k[H36[H37[]]]]].
    destruct H5 as [H5[]]. destruct H6 as [H6[]].
    rewrite H28,<-H35,H39,FT10_Lemma,FT10_Lemma; auto; pose proof MKT138; eauto;
    [ |rewrite H42|rewrite H40]; unfold Included; auto. clear H44. pose proof H5.
    apply (N'_extSeq_ran_Lemma _ k) in H44 as [H44[]]; auto. pose proof H6.
    apply (N'_extSeq_ran_Lemma _ k) in H47 as [H47[]]; auto.
    rewrite N'_Mult_Instantiate; auto. pose proof H30.
    apply (ωFun_Mult_P1 _ (((φ4⁻¹) ∘ g) ∘ k)) in H50 as [H50[]]; auto.
    apply (FT8 _ _ ω). split; auto. split; auto. repeat split; auto.
    assert (ω = \{ λ u, u ∈ ω /\ (((φ4⁻¹) ∘ f) ∘ k)[u]
      = ((Const (φ4⁻¹)[b]) · (((φ4⁻¹) ∘ g) ∘ k))[u] \})%ωfun.
    { apply AxiomI; split; intros.
      - apply AxiomII; repeat split; eauto. rewrite ωFun_Mult_P2,H34; auto.
        destruct H0 as [H0[]]. destruct H as [H[]].
        rewrite Q'_N_propersubset_Q'_N'_Lemma,Q'_N_propersubset_Q'_N'_Lemma,
        Q'_N_propersubset_Q'_N'_Lemma,Q'_N_propersubset_Q'_N'_Lemma; auto.
        assert (k[z] ∈ ω).
        { apply H38,(@ Property_ran z),Property_Value; try rewrite H37; auto. }
        rewrite <-H56 in H58. apply Property_Value in H58; auto.
        rewrite H1 in H58. apply AxiomII' in H58 as [_[]]; auto.
        assert (φ4[(φ4⁻¹)[f[k[z]]]] = φ4[((φ4⁻¹)[b] · (φ4⁻¹)[g[k[z]]])%ω]).
        { rewrite f11vi,φ4_PrMult,f11vi,f11vi; auto.
          rewrite H1; auto. rewrite <-H54 in H58.
          apply Property_Value,Property_ran,H55 in H58; auto.
          unfold Q'_N in H58. rewrite reqdi in H58.
          apply Property_Value,Property_ran in H58; auto.
          rewrite <-deqri,H14 in H58; auto. rewrite <-H56 in H58.
          apply Property_Value,Property_ran,H57 in H58; auto. }
        assert ((φ4⁻¹)[φ4[(φ4⁻¹)[f[k[z]]]]]
          = (φ4⁻¹)[(φ4[(φ4⁻¹)[b] · (φ4⁻¹)[g[k[z]]]])%ω]). { rewrite H60; auto. }
        rewrite f11iv,f11iv in H61; auto; rewrite H14. apply ω_Mult_in_ω.
        rewrite <-H14,deqri. apply (@ Property_ran b),Property_Value; auto.
        rewrite <-reqdi; auto. rewrite <-H14,deqri.
        apply (@ Property_ran g[k[z]]),Property_Value; auto. rewrite <-reqdi.
        apply H55,(@ Property_ran k[z]),Property_Value; try rewrite H54; auto.
        rewrite <-H14,deqri. apply (@ Property_ran f[k[z]]),Property_Value; auto.
        rewrite <-reqdi. apply H57,(@ Property_ran k[z]),
        Property_Value; try rewrite H56; auto.
      - apply AxiomII in H53; tauto. }
    rewrite <-H53. destruct NPAUF as [[_[]]_].
    apply AxiomII in H54 as [_[[_[_[]]]]]; auto. }
  rewrite H29; auto.
Qed.

(* 性质5: '分数列'值的一致性.

         对于分数列:
          f[n]
          ————    若该正分数列所有项都小于某一分数a/b,
          g[n]
                                  extf[N]
                  则其相应的延伸数列 ———————— 也小于该分数.
                                  extg[N]               *)
Property Q'_extNatSeq_Property5 : ∀ f g N a b, Q'_NatSeq f -> Q'_NatSeq g
  -> (∀ n, g[n] <> Q'0) -> N ∈ N' -> a ∈ Q'_N -> b ∈ Q'_N -> b <> Q'0
  -> (∀ n, n ∈ ω -> f[n]/g[n] < a/b)
  -> (Q'_extNatSeq f)[N] / (Q'_extNatSeq g)[N] < a/b.
Proof.
  intros. destruct φ4_is_Function as [[][]].
  assert (∀ M, (Q'_extNatSeq g)[M] <> Q'0).
  { intros. apply Q'_extNatSeq_Property3; auto. apply Q'0_in_Q'_N; auto. }
  assert (∀ n, n ∈ ω -> g[n] ∈ Q'_N).
  { intros. destruct H0 as [H0[]]. rewrite <-H13 in H12.
    apply Property_Value,Property_ran,H14 in H12; auto. }
  assert (∀ n, n ∈ ω -> f[n] ∈ Q'_N).
  { intros. destruct H as [H[]]. rewrite <-H14 in H13.
    apply Property_Value,Property_ran,H15 in H13; auto. }
  assert (∀ n, n ∈ ω -> Q'0 < g[n]).
  { intros. apply Q'_N_Q'0_is_FirstMember; auto.
    apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
    pose proof Q'0_in_Q'. apply MKT41 in H15; eauto. elim (H1 n); auto. }
  pose proof H. apply (Q'_extNatSeq_is_Function f) in H15 as [H15[]]; auto.
  pose proof H0. apply (Q'_extNatSeq_is_Function g) in H18 as [H18[]]; auto.
  assert (∀ N, N ∈ N' -> Q'0 < (Q'_extNatSeq g)[N]).
  { intros. apply Q'_N'_Q'0_is_FirstMember; auto.
    apply H20,(@ Property_ran N0),Property_Value; auto. rewrite H19; auto. }
  assert (Q'0 < b).
  { apply Q'_N_Q'0_is_FirstMember; auto. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. intro. pose proof Q'0_in_Q'.
    apply MKT41 in H22; eauto. }
  set (h := \{\ λ u v, u ∈ ω /\ v = a · g[u] \}\).
  assert (Q'_NatSeq h).
  { assert (Function h).
    { split; unfold Relation; intros. apply AxiomII in H23 as [_[x[y[]]]]; eauto.
      apply AxiomII' in H23 as [_[]]. apply AxiomII' in H24 as [_[]].
      rewrite H26,H25; auto. }
    split; auto. split. apply AxiomI; split; intros.
    apply AxiomII in H24 as [H24[]]. apply AxiomII' in H25; tauto.
    apply AxiomII; split; eauto. exists (a · g[z]). apply AxiomII'; split; auto.
    pose proof H3. apply (Q'_N_Mult_in_Q'_N a g[z]) in H25; auto.
    apply MKT49a; eauto. unfold Included; intros. apply AxiomII in H24 as [H24[]].
    apply AxiomII' in H25 as [H25[]]. rewrite H27. apply Q'_N_Mult_in_Q'_N; auto. }
  set (k := \{\ λ u v, u ∈ ω /\ v = b · f[u] \}\).
  assert (Q'_NatSeq k).
  { assert (Function k).
    { split; unfold Relation; intros. apply AxiomII in H24 as [_[x[y[]]]]; eauto.
      apply AxiomII' in H24 as [_[]]. apply AxiomII' in H25 as [_[]].
      rewrite H27,H26; auto. }
    split; auto. split. apply AxiomI; split; intros.
    apply AxiomII in H25 as [H25[]]. apply AxiomII' in H26; tauto.
    apply AxiomII; split; eauto. exists (b · f[z]).
    apply AxiomII'; split; auto. pose proof H4.
    apply (Q'_N_Mult_in_Q'_N b f[z]) in H26; auto.
    apply MKT49a; eauto. unfold Included; intros.
    apply AxiomII in H25 as [H25[]]. apply AxiomII' in H26 as [H26[]].
    rewrite H28. apply Q'_N_Mult_in_Q'_N; auto. }
  assert (∀ n, n ∈ ω -> h[n] ∈ Q'_N).
  { intros. destruct H23 as [H23[]]. rewrite <-H26 in H25.
    apply Property_Value,Property_ran,H27 in H25; auto. }
  assert (∀ n, n ∈ ω -> k[n] ∈ Q'_N).
  { intros. destruct H24 as [H24[]]. rewrite <-H27 in H26.
    apply Property_Value,Property_ran,H28 in H26; auto. }
  assert (∀ n, n ∈ ω -> k[n] < h[n]).
  { intros. destruct H23 as [H23[]]. destruct H24 as [H24[]].
    rewrite <-H28 in H27. apply Property_Value,AxiomII' in H27 as [_[]]; auto.
    rewrite <-H30 in H27. apply Property_Value,AxiomII' in H27 as [_[]]; auto.
    pose proof H27. apply H6,(Q'_Mult_PrOrder _ _ g[n]) in H27; auto with Q'.
    rewrite Q'_Divide_Property3,Q'_Mix_Association2,Q'_Mult_Commutation,<-H32
    in H27; auto. apply (Q'_Mult_PrOrder _ _ b) in H27; auto with Q'.
    rewrite <-H33,Q'_Divide_Property3 in H27; auto. }
  apply (Q'_extNatSeq_Property1 _ _ N) in H27; auto.
  assert ((Q'_extNatSeq g)[N] ∈ Q'_N').
  { apply H20,(@ Property_ran N),Property_Value; try rewrite H19; auto. }
  assert ((Q'_extNatSeq f)[N] ∈ Q'_N').
  { apply H17,(@ Property_ran N),Property_Value; try rewrite H16; auto. }
  assert (Q'0 < (Q'_extNatSeq g)[N]). { apply Q'_N'_Q'0_is_FirstMember; auto. }
  apply Q'_N'_propersubset_Q'_Z',Q'_Z'_propersubset_Q' in H28; auto.
  apply Q'_N'_propersubset_Q'_Z',Q'_Z'_propersubset_Q' in H29; auto.
  assert ((Q'_extNatSeq h)[N] = a · ((Q'_extNatSeq g)[N])
    /\ (Q'_extNatSeq k)[N] = b · ((Q'_extNatSeq f)[N])) as [].
  { split; apply Q'_extNatSeq_Property5_Lemma; auto. }
  rewrite H31,H32 in H27. apply (Q'_Mult_PrOrder _ _ (Q'_extNatSeq g)[N]);
  try apply Q'_Divide_in_Q'; auto.
  rewrite Q'_Divide_Property3,Q'_Mult_Commutation; auto with Q'.
  apply (Q'_Mult_PrOrder _ _ b); auto with Q'.
  rewrite <-Q'_Mult_Association,Q'_Divide_Property3; auto with Q'.
Qed.

(* 定义 *Q中的有理数列.  ω到*Q_Q的函数. *)
Definition Q'_RatSeq f := Function f /\ dom(f) = ω /\ ran(f) ⊂ Q'_Q.

(* 对于Q'_Q中任意正数, 总有唯一的最小分母的分数表示.
   即任意q, 总有唯一的Q'_N中的b, q = (q*b)/b 并且b小于所有使得 q=d/c 的c*)
Lemma RatSeq_and_NatSeq_Lemma : ∀ q, q ∈ Q'_Q -> Q'0 < q
  -> ∃! b, (b · q) ∈ Q'_N
    /\ FirstMember b Q'_Ord
      (\{ λ u, u ∈ Q'_N /\ u <> Q'0 /\ ∃ a, a ∈ Q'_N /\ q = a/u \}).
Proof.
  intros. pose proof Q'_Ord_WellOrder_Q'_N as [_ ].
  set (A := \{ λ u, u ∈ Q'_N /\ u <> Q'0 /\ ∃ a, a ∈ Q'_N /\ q = a/u \}).
  assert (A ⊂ Q'_N /\ A <> 0).
  { split; unfold Included; intros. apply AxiomII in H2; tauto.
    rewrite Q'_Q_equ_Q'_Z_Div in H; auto.
    apply AxiomII in H as [H[H2[a[b[H3[]]]]]]. apply MKT4' in H4 as [].
    assert (b <> Q'0).
    { intro. apply AxiomII in H6 as []. elim H8. pose proof Q'0_in_Q'.
      apply MKT41; eauto. }
    pose proof H3. apply Q'_Z_subset_Q' in H8; auto.
    pose proof H4. apply Q'_Z_subset_Q' in H9; auto.
    pose proof Q'0_in_Q'. pose proof Q'0_in_Q'_N.
    apply Q'_N_propersubset_Q'_Z in H11.
    assert (|a| ∈ Q'_Z).
    { assert (a ∈ Q' /\ Q'0 ∈ Q') as []; auto.
      apply (Q'_Ord_Tri a Q'0) in H12 as [H12|[]];
      [apply lt_Q'0_Q'Abs in H12|apply mt_Q'0_Q'Abs in H12|
       apply eq_Q'0_Q'Abs in H12| ]; try rewrite H12;
      try apply Q'_Z_Minus_in_Q'_Z; auto. }
    assert (|b| ∈ Q'_Z).
    { assert (b ∈ Q' /\ Q'0 ∈ Q') as []; auto.
      apply (Q'_Ord_Tri b Q'0) in H14 as [H14|[]];
      [apply lt_Q'0_Q'Abs in H14|apply mt_Q'0_Q'Abs in H14|
       apply eq_Q'0_Q'Abs in H14| ]; try rewrite H14;
      try apply Q'_Z_Minus_in_Q'_Z; auto. }
    assert (|a| ∈ Q'_N).
    { rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; repeat split; eauto.
      apply Q'0_le_Q'Abs in H8 as [_[]]; auto. }
    assert (|b| ∈ Q'_N).
    { rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; repeat split; eauto.
      apply Q'0_le_Q'Abs in H9 as [_[]]; auto. }
    pose proof H12. apply Q'_Z_subset_Q' in H16; auto.
    pose proof H13. apply Q'_Z_subset_Q' in H17; auto.
    assert (|b| <> Q'0). { intro. apply (eq_Q'0_Q'Abs b) in H18; auto. }
    assert (|a| = |b| · q).
    { apply mt_Q'0_Q'Abs in H0; auto. symmetry in H5.
      apply Q'_Divide_Mult in H5; auto. rewrite <-H0,<-Q'Abs_PrMult,H5; auto. }
    symmetry in H19. apply Q'_Divide_Mult in H19; auto.
    assert (|b| ∈ A). { apply AxiomII; repeat split; eauto. }
    intro. rewrite H21 in H20. elim (@ MKT16 |b|); auto. }
  destruct H2. apply H1 in H2; auto. destruct H2 as [b]. clear H3.
  exists b. pose proof H2 as []. apply AxiomII in H3 as [H3[H5[H6[a[]]]]].
  pose proof H. apply Q'_Q_subset_Q' in H9; auto. pose proof H5; pose proof H7.
  apply Q'_N_propersubset_Q'_Z,Q'_Z_subset_Q' in H10;
  apply Q'_N_propersubset_Q'_Z,Q'_Z_subset_Q' in H11; auto.
  symmetry in H8. apply Q'_Divide_Mult in H8; auto.
  repeat split; auto; [rewrite H8|destruct H2| ]; auto. intros x [].
  assert (b ∈ Q' /\ x ∈ Q') as [].
  { destruct H13. apply AxiomII in H13 as [_[]].
    apply Q'_N_propersubset_Q'_Z,Q'_Z_subset_Q' in H13; auto. }
  apply (Q'_Ord_Tri b x) in H14 as [H14|[]]; auto;
  clear H15; destruct H2,H13; [elim (H16 b)|elim (H4 x)]; auto.
Qed.

(* 对于正有理数列f, 存在两个自然数列h1 h2, 使得f[n] = h1[n]/h2[n].
   即 正有理数列可以用自然数列以分式的形式写出 *)
Property RatSeq_and_NatSeq : ∀ f, Q'_RatSeq f -> (∀ n, n ∈ ω -> Q'0 < f[n])
  -> ∃ h1 h2, Q'_NatSeq h1 /\ Q'_NatSeq h2 /\ (∀ n, h1[n] <> Q'0 /\ h2[n] <> Q'0)
    /\ (∀ n, n ∈ ω -> f[n] = h1[n]/h2[n]).
Proof.
  intros. destruct H as [H[]].
  assert (∀ n, n ∈ ω -> f[n] ∈ Q'_Q).
  { intros. rewrite <-H1 in H3.
    apply Property_Value,Property_ran,H2 in H3; auto. }
  set (A n := \{ λ u, u ∈ Q'_N /\ u <> Q'0 /\ ∃ a, (a ∈ Q'_N /\ f[n] = a/u) \}).
  set (h2 := \{\ λ u v, u ∈ ω /\ v = ∩(\{ λ w, (w · f[u]) ∈ Q'_N
    /\ FirstMember w Q'_Ord (A u) \}) \}\).
  set (h1 := \{\ λ u v, u ∈ ω /\ v = h2[u] · f[u] \}\).
  assert (∀ n, n ∈ ω -> ∃ b, Ensemble b /\ \{ λ w, (w · f[n]) ∈ Q'_N
    /\ FirstMember w Q'_Ord (A n) \} = [b]).
  { intros. pose proof H4. apply H3,RatSeq_and_NatSeq_Lemma in H4 as [b[[]]]; auto.
    exists b. assert (Ensemble b). { destruct H6. eauto. }
    split; auto. apply AxiomI; split; intros. apply AxiomII in H9 as [H9[]].
    apply MKT41; auto. symmetry. apply H7; auto. apply MKT41 in H9; auto.
    rewrite H9. apply AxiomII; auto. }
  assert (Q'_NatSeq h2).
  { assert (Function h2).
    { split; unfold Relation; intros. apply AxiomII in H5 as [_[x[y[]]]]; eauto.
      apply AxiomII' in H5 as [H5[]]. apply AxiomII' in H6 as [H6[]].
      rewrite H8,H10; auto. }
    split; auto. split; [(apply AxiomI; split)|unfold Included]; intros.
    - apply AxiomII in H6 as [H6[]]. apply AxiomII' in H7; tauto.
    - apply AxiomII; split; eauto. pose proof H6. apply H4 in H7 as [b[]].
      exists b. apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
      rewrite H8. symmetry. apply MKT44; auto.
    - apply AxiomII in H6 as [H6[]]. apply AxiomII' in H7 as [H7[]].
      pose proof H8. apply H4 in H10 as [b[]]. rewrite H11 in H9.
      apply MKT44 in H10 as [H10 _]. rewrite H10 in H9.
      assert (z ∈ [b]). { rewrite <-H9. apply MKT41; auto. }
      rewrite <-H11 in H12. apply AxiomII in H12 as [H12[_[]]].
      apply AxiomII in H13; tauto. }
  assert (∀ n, n ∈ ω -> h2[n] ∈ Q'_N /\ h2[n] <> Q'0 /\ (h2[n] · f[n]) ∈ Q'_N).
  { intros. destruct H5 as [H5[]]. rewrite <-H7 in H6.
    apply Property_Value in H6; auto. apply AxiomII' in H6 as [H6[]].
    pose proof H9. apply H4 in H11 as [b[]].
    rewrite H12 in H10. assert (b ∈ [b]). { apply MKT41; auto. }
    rewrite <-H12 in H13. apply AxiomII in H13 as [_[]].
    destruct H14. apply AxiomII in H14 as [_[H14[]]].
    apply MKT44 in H11 as [H11 _]. rewrite H10,H11; auto. }
  assert (Q'_NatSeq h1).
  { assert (Function h1).
    { split; unfold Relation; intros. apply AxiomII in H7 as [_[x[y[]]]]; eauto.
      apply AxiomII' in H7 as [H7[]]. apply AxiomII' in H8 as [H8[]].
      rewrite H10,H12; auto. }
    split; auto. split; [(apply AxiomI; split)|unfold Included]; intros.
    - apply AxiomII in H8 as [H8[]]. apply AxiomII' in H9; tauto.
    - apply AxiomII; split; eauto. exists (h2[z] · f[z]).
      apply AxiomII'; split; auto. pose proof H8.
      apply H6 in H9 as [_[]]. apply MKT49a; eauto.
    - apply AxiomII in H8 as [H8[]]. apply AxiomII' in H9 as [H9[]].
      apply H6 in H10 as [_[]]. rewrite H11; auto. }
  assert (∀ n, n ∈ ω -> h1[n] ∈ Q'_N /\ h1[n] <> Q'0).
  { intros. destruct H7 as [H7[]]. rewrite <-H9 in H8.
    apply Property_Value in H8; auto. apply AxiomII' in H8 as [H8[]].
    pose proof H11. apply H6 in H11 as [H11[]]. split.
    rewrite H12; auto. intro. rewrite H16 in H12. symmetry in H12.
    apply Q'_Mult_Property3 in H12 as []; auto;
    [ |apply Q'_Z_subset_Q',Q'_N_propersubset_Q'_Z|
     apply Q'_Q_subset_Q',H3]; auto. pose proof (H0 n). rewrite H12 in H17.
     elim (Q'_Ord_irReflex Q'0 Q'0); try apply Q'0_in_Q'; auto. }
  exists h1,h2. split; auto. split; auto. split; intros.
  - destruct (classic (n ∈ ω)).
    + pose proof H9. apply H6 in H9 as [H9[]]; apply H8 in H10 as []; auto.
    + destruct H5 as [_[]]. destruct H7 as [_[]]. pose proof H9.
      rewrite <-H5 in H9. rewrite <-H7 in H12.
      apply MKT69a in H9; apply MKT69a in H12; auto.
      rewrite H9,H12. pose proof Q'0_in_Q'.
      split; intro; elim MKT39; rewrite H14; eauto.
  - pose proof H9. pose proof H9.
    apply H6 in H9 as [H9[]]. apply H8 in H10 as [].
    apply Q'_N_propersubset_Q'_Z,Q'_Z_subset_Q' in H9;
    apply Q'_N_propersubset_Q'_Z,Q'_Z_subset_Q' in H10; auto.
    destruct H7 as [H7[]]. rewrite <-H15 in H11.
    apply Property_Value,AxiomII' in H11 as [H11[]]; auto.
    apply H3,Q'_Q_subset_Q' in H17; auto. symmetry in H18.
    apply Q'_Divide_Mult in H18; auto.
Qed.

Open Scope r_scope.

(* 定义 R中的有理数列.  ω到Q的函数. *)
Definition R_RatSeq f := Function f /\ dom(f) = ω /\ ran(f) ⊂ Ｑ.

(* 引理, 任何有理数(Q中的元)可以用某一唯一的*Q_Q中的元来表示.
        这实际上是一个从等价类中选代表的过程 *)
Lemma Q'_RatSeq_and_R_RatSeq_Lemma : ∀ q, q ∈ Ｑ
  -> ∃! q', q' ∈ Q'_Q /\ q = \[q'\].
Proof.
  intros. pose proof H. apply AxiomII in H0 as [H0[x[]]]. exists x.
  split; auto. intros x' []. destruct (classic (x=x')); auto.
  rewrite H2 in H4. pose proof H1; pose proof H3.
  apply Q'_Q_subset_Q'_Arch in H6; apply Q'_Q_subset_Q'_Arch in H7; auto.
  apply R_Q'_Property in H4; auto. pose proof H1; pose proof H3.
  apply Q'_Q_subset_Q' in H8; apply Q'_Q_subset_Q' in H9; auto.
  set (a := (x - x')%q').
  assert (a ∈ Q'_Q). { apply Q'_Q_Minus_in_Q'_Q; auto. }
  pose proof H10. apply Q'_Q_subset_Q' in H11; auto.
  assert (a <> Q'0).
  { intro. pose proof Q'0_in_Q'. apply Q'_Minus_Plus in H12; auto.
    rewrite Q'_Plus_Property in H12; auto. }
  pose proof H11. apply Q'_Inv in H13 as [a'[[H13[]]_]]; auto.
  pose proof Q'0_in_Q'. pose proof Q'1_in_Q'.
  pose proof H10. rewrite Q'_Q_equ_Q'_Z_Div in H18; auto.
  apply AxiomII in H18 as [_[H18[u[v[H19[]]]]]].
  apply MKT4' in H20 as []. apply AxiomII in H22 as [_ ].
  assert (v <> Q'0). { intro. elim H22. apply MKT41; eauto. }
  pose proof H19; pose proof H20.
  apply Q'_Z_subset_Q' in H24; apply Q'_Z_subset_Q' in H25; auto. symmetry in H21.
  assert (u <> Q'0).
  { intro. rewrite H26 in H21.
    apply Q'_Divide_Mult,Q'_Mult_Property3 in H21 as []; auto. }
  assert (a' ∈ Q'_Q).
  { rewrite Q'_Q_equ_Q'_Z_Div; auto. apply AxiomII; repeat split; eauto.
    exists v,u. repeat split; auto. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. intro. apply MKT41 in H27; eauto.
    apply Q'_Divide_Mult in H21; auto. symmetry.
    apply (Q'_Divide_Mult _ a'); auto.
    rewrite <-H21,Q'_Mult_Association,H15,Q'_Mult_Property2; auto. }
  destruct NPAUF as [_]. apply I_Inv_Property1 in H15; auto.
  apply MKT4' in H15 as []. apply AxiomII in H29 as []. elim H30.
  apply Q'_Q_subset_Q'_Arch; auto. apply MKT4'; split; auto.
  apply AxiomII; split; eauto. intro. apply MKT41 in H29; eauto.
Qed.

(* 对于R中的有理数列f, 存在*Q中的有理数列h, 使得f[n] = [h[n]] (h[n] 代表的等价类) *)
Property Q'_RatSeq_and_R_RatSeq : ∀ f, R_RatSeq f
  -> ∃ h, Q'_RatSeq h /\ (∀ n, n ∈ ω -> f[n] = \[h[n]\]).
Proof.
  intros. destruct H as [H[]].
  set (h := \{\ λ u v, u ∈ ω /\ v = ∩(\{ λ w, w ∈ Q'_Q /\ f[u] = \[w\] \}) \}\).
  assert (∀ n, n ∈ ω
    -> ∃ q, Ensemble q /\ \{ λ w, w ∈ Q'_Q /\ f[n] = \[w\] \} = [q]).
  { intros. rewrite <-H0 in H2.
    apply Property_Value,Property_ran,H1 in H2; auto. pose proof H2.
    apply Q'_RatSeq_and_R_RatSeq_Lemma in H3 as [x[[]]]; auto.
    exists x. split; eauto. apply AxiomI; split; intros.
    apply AxiomII in H6 as [H6[]]. apply MKT41; eauto. symmetry.
    apply H5; auto. apply MKT41 in H6; eauto. rewrite H6.
    apply AxiomII; split; eauto. } exists h.
  assert (Q'_RatSeq h) as [H3[]].
  { assert (Function h).
    { split; unfold Relation; intros. apply AxiomII in H3 as [_[x[y[]]]]; eauto.
      apply AxiomII' in H3 as [_[]]. apply AxiomII' in H4 as [_[]].
      rewrite H5,H6; auto. }
    split; auto. split; [(apply AxiomI; split)|unfold Included]; intros.
    - apply AxiomII in H4 as [H4[]]. apply AxiomII' in H5; tauto.
    - apply AxiomII; split; eauto. pose proof H4.
      apply H2 in H5 as [q[]]. exists (∩[q]).
      apply AxiomII'; split; [ |rewrite H6]; auto. pose proof H5.
      apply MKT44 in H5 as [H5 _]. rewrite H5. apply MKT49a; eauto.
    - apply AxiomII in H4 as [H4[]]. apply AxiomII' in H5 as [H5[]].
      pose proof H6. apply H2 in H8 as [q[]]. rewrite H9 in H7.
      pose proof H8. apply MKT44 in H8 as [H8 _]. rewrite H7,H8.
      assert (q ∈ [q]). { apply MKT41; eauto. }
      rewrite <-H9 in H11. apply AxiomII in H11; tauto. }
  split; intros. split; auto. rewrite <-H4 in H6.
  apply Property_Value in H6; auto. apply AxiomII' in H6 as [H6[]].
  pose proof H7. apply H2 in H9 as [q[]]. pose proof H9.
  apply MKT44 in H11 as [H11 _]. assert (q ∈ [q]). { apply MKT41; eauto. }
  rewrite H10,H11 in H8. rewrite <-H10 in H12.
  rewrite H8. apply AxiomII in H12; tauto.
Qed.

(* 定义 R中的数列. *)
Definition R_Seq f := Function f /\ dom(f) = ω /\ ran(f) ⊂ Ｒ.

(* 定义 R中数列的子列. h是f的子列. *)
Definition R_subSeq h f := R_Seq f /\ ∃ g, ω_Seq g
  /\ (∀ m n, m ∈ ω -> n ∈ ω -> m ∈ n -> g[m] ∈ g[n])
  /\ h = \{\ λ u v, u ∈ ω /\ v = f[g[u]] \}\.

Property R_subSeq_Property : ∀ h f, R_subSeq h f -> R_Seq h.
Proof.
  intros. destruct H as [[H[]][g[[H2[]][]]]].
  assert (Function h).
  { rewrite H6. split; unfold Relation; intros.
    apply AxiomII in H7 as [_[x[y[]]]]; eauto.
    apply AxiomII' in H7 as [H7[]].
    apply AxiomII' in H8 as [H8[]]. rewrite H10,H12; auto. }
  split; auto. split; [(apply AxiomI; split)|
  unfold Included]; intros.
  - apply AxiomII in H8 as [H8[]]. rewrite H6 in H9.
    apply AxiomII' in H9; tauto.
  - apply AxiomII; split; eauto. exists (f[g[z]]).
    rewrite H6. apply AxiomII'; split; auto. pose proof H8.
    rewrite <-H3 in H8. apply Property_Value,Property_ran,H4 in H8;
    auto. rewrite <-H0 in H8. apply Property_Value,Property_ran
    in H8; auto. apply MKT49a; eauto.
  - apply AxiomII in H8 as [H8[]]. rewrite H6 in H9.
    apply AxiomII' in H9 as [H9[]]. rewrite <-H3 in H10.
    apply Property_Value,Property_ran,H4 in H10; auto.
    rewrite <-H0 in H10. apply Property_Value,Property_ran,H1
    in H10; auto. rewrite H11; auto.
Qed.

(* 数列与子列的关系 若h是f的子列, 则对任意f的第n项f[n],
   总有更靠后的一项f[m](m > n)是子列中的某一项h[w], 即f[m] = h[w]
   这里体现了子列项数的无限性*)
Property R_Seq_Property1 : ∀ h f n, R_subSeq h f -> n ∈ ω
  -> ∃ m w, m ∈ ω /\ w ∈ ω /\ n ∈ m /\ f[m] = h[w].
Proof.
  intros. pose proof H. apply R_subSeq_Property in H1 as [H1[]].
  destruct H as [[H[]][g[[H6[]][]]]].
  assert (∀ n, n ∈ ω -> g[n] ∈ ω).
  { intros. rewrite <-H7 in H11.
    apply Property_Value,Property_ran,H8 in H11; auto. }
  assert (∀ n, n ∈ ω -> f[n] ∈ Ｒ).
  { intros. rewrite <-H4 in H12.
    apply Property_Value,Property_ran,H5 in H12; auto. }
  assert (∀ n, n ∈ ω -> h[n] ∈ Ｒ).
  { intros. rewrite <-H2 in H13.
    apply Property_Value,Property_ran,H3 in H13; auto. }
  assert (∀ n, n ∈ ω -> h[n] = f[g[n]]).
  { intros. rewrite <-H2 in H14. apply Property_Value in H14; auto.
    rewrite H10 in H14. apply AxiomII' in H14 as [_[]].
    rewrite H10; auto. }
  destruct (classic (n ∈ ran(g))).
  - apply AxiomII in H15 as [H15[]]. pose proof H16.
    rewrite MKT70 in H16; auto. apply AxiomII' in H16 as [].
    apply Property_dom in H17. rewrite H7 in H17. pose proof H17.
    apply MKT134 in H17. assert (x ∈ (PlusOne x)).
    { apply MKT4; right. apply MKT41; eauto. }
    apply H9 in H20; auto. exists (g[PlusOne x]),(PlusOne x).
    repeat split; auto. rewrite H18; auto. rewrite H14; auto.
  - assert ((∃ a, a ∈ ω /\ a ∈ n /\ a ∈ ran(g))
      \/ (∃ b, b ∈ ω /\ n ∈ b /\ b ∈ ran(g)))
    as [[a[H16[]]]|[b[H16[]]]].
    { apply NNPP; intro. assert (∀ m, m ∈ ω -> ~ m ∈ ran(g)).
      { intros. assert (Ordinal m /\ Ordinal n) as [].
        { apply AxiomII in H0 as [_[]].
          apply AxiomII in H17 as [_[]]; auto. }
        apply (@ MKT110 m n) in H18 as [H18|[]];
        try rewrite H18; auto; intro; elim H16; eauto. }
      assert (ran(g) = 0).
      { apply AxiomI; split; intro; elim (@ MKT16 z); auto.
        pose proof H18. apply H8 in H18. elim (H17 z); auto. }
      rewrite <-H7 in H0. apply Property_Value,Property_ran
      in H0; auto. rewrite H18 in H0. elim (@ MKT16 g[n]); auto. }
    + set (A := \{ λ u, u ∈ ω /\ u ∈ n /\ u ∈ ran(g) \}).
      assert (WellOrdered E⁻¹ A).
      { assert (A ⊂ n).
        { unfold Included; intros. apply AxiomII in H19; tauto. }
        apply (wosub n); auto. apply AxiomII in H0 as [_[]]; auto. }
      assert (A ⊂ A /\ A <> 0).
      { split; unfold Included; auto. intro.
        assert (a ∈ A). { apply AxiomII; split; eauto. }
        rewrite H20 in H21. elim (@ MKT16 a); auto. }
      destruct H19. destruct H20. apply H21 in H20 as []; auto.
      clear dependent a. clear H22. destruct H20.
      apply AxiomII in H16 as [_[H16[]]].
      apply AxiomII in H20 as [_[]]. pose proof H20.
      rewrite MKT70 in H20; auto. apply AxiomII' in H20 as [].
      apply Property_dom in H22. rewrite H7 in H22.
      pose proof H22. apply MKT134 in H22.
      assert (n ∈ g[PlusOne x0]).
      { assert (Ordinal n /\ Ordinal (g[PlusOne x0])) as [].
        { apply AxiomII in H0 as [_[]].
          apply H11,AxiomII in H22 as [_[]]; auto. }
        apply (@ MKT110 n g[PlusOne x0]) in H25 as [H25|[]];
        auto; clear H26.
        - assert (g[PlusOne x0] ∈ A).
          { apply AxiomII; repeat split; eauto. rewrite <-H7 in H22.
            apply Property_Value,Property_ran in H22; auto. }
          apply H17 in H26. elim H26. apply AxiomII'; split.
          apply MKT49a; eauto. apply AxiomII'; split.
          apply MKT49a; eauto. rewrite H23. apply H9; auto.
          apply MKT4; right. apply MKT41; eauto.
        - rewrite <-H7 in H22. apply Property_Value,Property_ran
          in H22; auto. elim H15. rewrite H25; auto. }
      exists (g[PlusOne x0]),(PlusOne x0).
      repeat split; auto. rewrite H14; auto.
    + apply AxiomII in H18 as [_[]]. pose proof H18.
      rewrite MKT70 in H18; auto. apply AxiomII' in H18 as [].
      apply Property_dom in H19. rewrite H7 in H19. exists b,x.
      repeat split; auto. rewrite H14; auto. rewrite H20; auto.
Qed.

(* 定义 实数的单增 *)
Definition R_monoIncrease f := ∀ m n, m ∈ ω -> n ∈ ω
  -> m ∈ n -> f[m] = f[n] \/ f[m] < f[n].

(* 定义 实数的严格单增 *)
Definition R_strictly_monoIncrease f := ∀ m n, m ∈ ω -> n ∈ ω
  -> m ∈ n -> f[m] < f[n].

(* 非严格单增数列可以推出两种情形：
      1. 数列从某项起恒为常数
      2. 数列有严格的单增子列 *)
Property R_Seq_Property2 : ∀ f, R_Seq f -> R_monoIncrease f
  -> (∃ n r, n ∈ ω /\ r ∈ Ｒ /\ (∀ m, m ∈ ω -> n ∈ m -> f[m] = r))
  \/ (∃ h, R_subSeq h f /\ R_strictly_monoIncrease h).
Proof.
  intros. destruct (classic (∃n r, n ∈ ω /\ r ∈ Ｒ
    /\ (∀ m, m ∈ ω -> n ∈ m -> f [m] = r))); auto.
  destruct H as [H[]]. assert (∀ m, m ∈ ω -> f[m] ∈ Ｒ).
  { intros. rewrite <-H2 in H4.
    apply Property_Value,Property_ran,H3 in H4; auto. }
  assert (∀ n, n ∈ ω -> ∃ m, m ∈ ω /\ n ∈ m /\ f[n] < f[m]).
  { intros. apply NNPP; intro. elim H1. exists n,f[n].
    repeat split; auto. intros. pose proof H8.
    apply H0 in H8 as []; auto. elim H6; eauto. }
  clear H1. set (A w := \{ λ u, u ∈ ω /\ f[u] = w \}).
  set (B := \{ λ u, ∃ w, w ∈ ran(f) /\ FirstMember u E (A w) \}).
  set (f1 := Restriction f B). assert (Function1_1 f1).
  { split. apply MKT126a; auto. split; unfold Relation; intros.
    apply AxiomII in H1 as [_[x[y[]]]]; eauto.
    apply AxiomII' in H1 as []. apply AxiomII' in H6 as [].
    apply MKT4' in H7 as []. apply MKT4' in H8 as [].
    apply AxiomII' in H9 as [H9[]]. apply AxiomII' in H10 as [H10[]].
    apply AxiomII in H11 as [H11[w1[H16[]]]].
    apply AxiomII in H13 as [H13[w2[H18[]]]].
    apply AxiomII in H15 as [_[]]. apply AxiomII in H19 as [_[]].
    pose proof H7. pose proof H8. apply Property_dom,Property_Value in H23;
    apply Property_dom,Property_Value in H24; auto.
    assert (f[y] = x /\ f[z] = x) as [].
    { destruct H. split; [apply (H25 y)|apply (H25 z)]; auto. }
    assert (w1 = w2). { rewrite H26,<-H25,H21 in H22; auto. }
    assert (Ordinal y /\ Ordinal z) as [].
    { apply AxiomII in H15 as [_[]]. apply AxiomII in H19 as [_[]]. auto. }
    apply (@ MKT110 y z) in H28 as [H28|[]]; auto; clear H29.
    assert (y ∈ (A w2)). { rewrite <-H27. apply AxiomII; auto. }
    apply H20 in H29. elim H29. apply AxiomII'; split; try apply  MKT49; auto.
    assert (z ∈ (A w1)). { rewrite H27. apply AxiomII; auto. }
    apply H17 in H29. elim H29. apply AxiomII'; split; try apply MKT49; auto. }
  assert (dom(f1) = B /\ ran(f1) = ran(f)) as [].
  { pose proof H. apply (MKT126a f B) in H.
    pose proof H6. apply (MKT126b f B) in H7.
    assert (∀ y, y ∈ dom(Restriction f B) -> (Restriction f B)[y] = f[y]).
    { apply (MKT126c f B); auto. }
    assert (B ∩ dom(f) = B).
    { apply AxiomI; split; intros. apply MKT4' in H9; tauto.
      apply MKT4'; split; auto. apply AxiomII in H9 as [H9[w[H10[]]]].
      apply AxiomII in H11 as [H11[]]. rewrite H2; auto. }
    assert (dom(f1) = B). { rewrite <-H9; auto. }
    split; auto. apply AxiomI; split; intros.
    - apply AxiomII in H11 as [H11[]]. assert (z = f1[x]).
      { pose proof H12. apply Property_dom,Property_Value in H13; auto.
        destruct H1 as [[]]. apply (H14 x); auto. }
      apply Property_dom in H12. pose proof H12. apply H8 in H12.
      unfold f1 in H13. rewrite H13,H12. rewrite H10,<-H9 in H14.
      apply MKT4' in H14 as []. apply Property_Value,Property_ran in H15; auto.
    - apply AxiomII in H11 as [H11[]]. assert (z = f[x]).
      { destruct H6. apply (H13 x); auto. apply Property_dom in H12.
        apply Property_Value; [(split)| ]; auto. }
      assert (Ensemble x). { apply Property_dom in H12; eauto. }
      assert (x ∈ (A z)).
      { apply AxiomII; repeat split; auto.
        apply Property_dom in H12. rewrite <-H2; auto. }
      assert (WellOrdered E (A z)) as [_ H16].
      { apply (wosub ω); auto. apply MKT107. pose proof MKT138.
        apply AxiomII in H16; tauto. unfold Included; intros.
        apply AxiomII in H16; tauto. }
      assert ((A z) ⊂ (A z) /\ A z <> 0).
      { split; unfold Included; auto; intro.
        rewrite H17 in H15. elim (@ MKT16 x); auto. }
      destruct H17. apply H16 in H17; auto; clear H18. destruct H17 as [a].
      assert (Ensemble a). { destruct H17; eauto. }
      assert (a ∈ B).
      { apply AxiomII; split; auto. exists z. split; auto.
        apply Property_ran in H12; auto. }
      rewrite <-H10 in H19. pose proof H19. destruct H1.
      apply H8 in H19. apply Property_Value,Property_ran in H20; auto.
      destruct H17. apply AxiomII in H17 as [_[]]. rewrite <-H23,<-H19; auto. }
  assert (∀u v, u ∈ dom(f1) -> v ∈ dom(f1) -> Rrelation u E v
    -> f1[u] < f1[v]).
  { intros. pose proof H. apply (MKT126a f B) in H. pose proof H11.
    apply (MKT126b f B) in H12.
    assert (∀ y, y ∈ dom(Restriction f B) -> (Restriction f B)[y] = f[y]).
    { apply (MKT126c f B); auto. }
    pose proof H8; pose proof H9. apply H13 in H14; apply H13 in H15.
    pose proof H8; pose proof H9. rewrite H6 in H16,H17.
    apply AxiomII in H16 as [_[x[H16[]]]].
    apply AxiomII in H17 as [_[y[H17[]]]].
    apply AxiomII in H18 as [_[]]. apply AxiomII in H20 as [_[]].
    apply AxiomII' in H10 as [_ H10]. unfold f1. rewrite H14,H15.
    pose proof H10. apply H0 in H10 as []; auto.
    assert (u = v).
    { assert (f1⁻¹[f1[u]] = f1⁻¹[f1[v]]).
      { unfold f1. rewrite H14,H15,H10; auto. }
      destruct H1. rewrite f11iv,f11iv in H25; auto. }
    rewrite H25 in H24. elim (MKT101 v); auto. }
  assert (B ⊂ ω).
  { unfold Included; intros. apply AxiomII in H9 as [_[a[_[]]]].
    apply AxiomII in H9; tauto. }
  assert (WellOrdered E ω /\ WellOrdered E B).
  { pose proof MKT138. apply AxiomII in H10 as [].
    apply MKT107 in H11. split; auto. apply (wosub ω); auto. }
  destruct H10. apply (@ MKT99 E E ω B) in H10; auto; clear H11.
  destruct H10 as [g[H10[]]].
  assert (dom(g) = ω /\ ran(g) = B) as [].
  { destruct H11 as [H11[H13[H14[]]]]. destruct H12; split; auto.
    - apply NNPP; intro.
      assert (rSection ran(g) E B /\ ran(g) <> B); auto.
      destruct H18. apply MKT91 in H18; auto; clear H19.
      destruct H18 as [x[]].
      assert (ran(g) ⊂ x /\ ran(g) <> 0).
      { split; unfold Included; intros. rewrite H19 in H20.
        apply AxiomII in H20 as [_[]]. apply AxiomII' in H21; tauto.
        intro. pose proof in_ω_0. rewrite <-H12 in H21.
        apply Property_Value,Property_ran in H21; auto.
        rewrite H20 in H21. elim (@ MKT16 g[0]); auto. }
      pose proof H18. apply H9,AxiomII in H21 as [_[H21[]]].
      destruct H20. apply H23 in H20; auto. clear H24.
      destruct H20 as [a]. assert (Function1_1 g) as [_ H24].
      { apply (MKT96 g E E); auto. }
      destruct H20. pose proof H20. rewrite reqdi in H20.
      apply Property_Value,Property_ran in H20; auto.
      rewrite <-deqri,H12 in H20. pose proof H20. apply MKT134 in H27.
      assert ((g⁻¹)[a] ∈ (PlusOne (g⁻¹)[a])).
      { apply MKT4; right. apply MKT41; eauto. }
      destruct H14 as [_[_[]]].
      assert (Rrelation g[(g⁻¹)[a]] E g[(PlusOne (g⁻¹)[a])]).
      { apply H29; try rewrite H12; auto.
        apply AxiomII'; split; try apply MKT49a; eauto. }
      rewrite f11vi in H30; auto. apply AxiomII' in H30 as [].
      apply MKT49b in H30 as []. rewrite <-H12 in H27.
      apply Property_Value,Property_ran in H27; auto.
      apply H25 in H27. elim H27. apply AxiomII'; split; [apply MKT49a| ]; auto.
      apply AxiomII'; split; auto.
    - apply NNPP; intro.
      assert (rSection dom(g) E ω /\ dom(g) <> ω) as []; auto.
      apply MKT91 in H18; auto; clear H19. destruct H18 as [x[]].
      assert (dom(g) = x).
      { rewrite H19. apply AxiomI; split; intros.
        apply AxiomII in H20 as [_[]]. apply AxiomII' in H21; tauto.
        pose proof MKT138. apply AxiomII in H21 as [_[]].
        apply AxiomII; repeat split; [eauto|eapply H22| ]; eauto.
        apply AxiomII'; split; try apply MKT49a; eauto. } clear H19.
      pose proof H18. apply AxiomII in H19 as [_[_[]]].
      assert (x ⊂ x /\ x <> 0) as [].
      { split; unfold Included; auto; intro. rewrite <-H20 in H22.
        assert (ran(g) = 0).
        { apply NNPP; intro. apply NEexE in H23 as [z].
          apply AxiomII in H23 as [_[]]. apply Property_dom in H23.
          rewrite H22 in H23. elim (@ MKT16 x0); auto. }
        rewrite H12,<-H6 in H23. assert (ran(f1) = 0).
        { apply NNPP; intro. apply NEexE in H24 as [z].
          apply AxiomII in H24 as [_[]]. apply Property_dom in H24.
          rewrite H23 in H24. elim (@ MKT16 x0); auto. }
        rewrite H7 in H24. assert (dom(f) = 0).
        { apply NNPP; intro. apply NEexE in H25 as [z].
          apply AxiomII in H25 as [_[]]. apply Property_ran in H25.
          rewrite H24 in H25. elim (@ MKT16 x0); auto. }
        rewrite H2 in H25. pose proof in_ω_0.
        rewrite H25 in H26. elim (@ MKT16 0); auto. }
      apply H21 in H22; auto; clear H23. destruct H22 as [a].
      assert (FirstMember g[a] E⁻¹ B).
      { rewrite <-H12. destruct H22. rewrite <-H20 in H22.
        pose proof H22. apply Property_Value,Property_ran in H22; auto.
        split; intros; auto. intro. apply AxiomII' in H26 as [].
        apply AxiomII' in H27 as []. rewrite H20 in H24.
        assert (Function1_1 g) as [_ H29]. { apply (MKT96 g E E); auto. }
        rewrite reqdi in H25. pose proof H25.
        apply Property_Value,Property_ran in H25; auto.
        rewrite <-deqri,H20 in H25. pose proof H25.
        apply H23 in H31. elim H31. apply AxiomII'; split.
        apply MKT49a; eauto. apply AxiomII'; split.
        apply MKT49a; eauto. apply MKT96b in H14 as [_[_[]]].
        assert (Rrelation (g⁻¹)[g[a]] E (g⁻¹)[y]).
        { apply H32; auto. rewrite <-H20 in H24.
          apply Property_Value,Property_ran in H24; auto.
          rewrite reqdi in H24; auto. apply AxiomII'; auto. }
        rewrite f11iv in H33; auto. apply AxiomII' in H33; tauto.
        rewrite H20; auto. }
      assert (∀ n, n ∈ dom(f1) -> ∃ m, m ∈ dom(f1) /\ n ∈ m /\ f1[n] < f1[m]).
      { intros. pose proof H24. rewrite H6 in H25. pose proof H25.
        apply H9 in H26. apply H5 in H26 as [x0[H26[]]].
        pose proof H. apply (MKT126a f B) in H29.
        pose proof H. apply (MKT126b f B) in H30.
        assert (∀ y, y ∈ dom(Restriction f B)
          -> (Restriction f B)[y] = f[y]). { apply MKT126c; auto. }
        assert (f[x0] ∈ ran(f)).
        { apply (@ Property_ran x0),Property_Value; auto. rewrite H2; auto. }
        assert (WellOrdered E (A f[x0])).
        { apply (wosub ω); auto. unfold Included; intros.
          apply AxiomII in H33; tauto. }
        assert ((A f[x0]) ⊂ (A f[x0]) /\ (A f[x0]) <> 0).
        { split; unfold Included; auto; intro.
          assert (x0 ∈ (A f[x0])). { apply AxiomII; split; eauto. }
          rewrite H34 in H35. elim (@ MKT16 x0); auto. }
        destruct H33,H34. apply H35 in H34; auto; clear H36.
        destruct H34 as []. assert (f[x0] = f[x1]).
        { destruct H34. apply AxiomII in H34 as [H34[]]; auto. }
        assert (x1 ∈ dom(f1)).
        { unfold f1. rewrite H30,H2. pose proof H34. destruct H34.
          apply AxiomII in H34 as [H34[]]. apply MKT4'; split; auto.
          apply AxiomII; split; eauto. }
        pose proof H37. apply H31 in H38. pose proof H24.
        apply H31 in H24. rewrite <-H24,H36,<-H38 in H28. exists x1.
        repeat split; auto. pose proof H37. unfold f1 in H37.
        rewrite H30 in H37. apply MKT4' in H37 as [].
        apply H9 in H25; apply H9 in H37.
        assert (Ordinal n /\ Ordinal x1) as [].
        { apply AxiomII in H25 as [H25[]].
          apply AxiomII in H37 as [H37[]]; auto. }
        apply (@ MKT110 n x1) in H42 as [H42|[]]; auto; clear H43.
        - assert (Rrelation x1 E n).
          { apply AxiomII'; split; auto. apply MKT49a; eauto. }
          apply H8 in H43; auto. unfold f1 in H43.
          rewrite H24,H38 in H28,H43. apply (R_Ord_Trans f[n]) in H43; auto.
          elim (R_Ord_irReflex f[n] f[n]); auto.
        - rewrite H24,H38,H42 in H28.
          elim (R_Ord_irReflex f[x1] f[x1]); auto. }
      destruct H23. pose proof H23. rewrite <-H6 in H26.
      apply H24 in H26 as [x0[H26[]]]. rewrite H6 in H26.
      pose proof H26. apply H25 in H26. elim H26.
      apply AxiomII'; split. apply MKT49a; eauto.
      apply AxiomII'; split; auto. apply MKT49a; eauto. } clear H12.
  set (h := \{\ λ u v, u ∈ ω /\ v = f[g[u]] \}\).
  right. exists h. split.
  - split. split; auto. exists g. split. rewrite <-H14 in H9.
    split; auto. split; auto. intros. destruct H11 as [_[_[]]].
    destruct H11 as [_[_[]]]. assert (Rrelation g[m] E g[n]).
    { apply H18; try rewrite H13; auto.
      apply AxiomII'; split; auto. apply MKT49a; eauto. }
    apply AxiomII' in H19; tauto.
  - unfold R_strictly_monoIncrease; intros.
    assert (Function h).
    { split; unfold Relation; intros. apply AxiomII in H17 as [_[x[y[]]]]; eauto.
      apply AxiomII' in H17 as [H17[]]. apply AxiomII' in H18 as [H18[]].
      rewrite H20,H22; auto. }
    assert (dom(h) = ω).
    { apply AxiomI; split; intros.
      - apply AxiomII in H18 as [H18[]]. apply AxiomII' in H19; tauto.
      - apply AxiomII; split; eauto. exists f[g[z]].
        apply AxiomII'; split; auto. pose proof H18.
        rewrite <-H13 in H19. apply Property_Value,Property_ran in H19; auto.
        rewrite H14,<-H6 in H19. pose proof H. apply (MKT126a f B) in H.
        pose proof H20. apply (MKT126b f B) in H20.
        assert (∀ y, y ∈ dom(Restriction f B)
          -> (Restriction f B)[y] = f[y]). { apply MKT126c; auto. }
        pose proof H19. apply H22 in H19. destruct H1.
        apply Property_Value,Property_ran in H23; auto.
        rewrite <-H19. apply MKT49a; eauto. }
    rewrite <-H18 in H12,H15. apply Property_Value,AxiomII' in H12 as [H12[]];
    apply Property_Value,AxiomII' in H15 as [H15[]]; auto.
    rewrite <-H13 in H19,H21. pose proof H19; pose proof H21.
    apply Property_Value,Property_ran in H19;
    apply Property_Value,Property_ran in H21; auto.
    rewrite H14,<-H6 in H19,H21. pose proof H. apply (MKT126a f B) in H.
    pose proof H25. apply (MKT126b f B) in H25.
    assert (∀ y, y ∈ dom(Restriction f B)
          -> (Restriction f B)[y] = f[y]). { apply MKT126c; auto. }
    pose proof H19; pose proof H21. apply H27 in H19; apply H27 in H21.
    rewrite H20,H22,<-H19,<-H21. apply H8; auto. destruct H11 as [_[_[]]].
    destruct H11 as [_[_[]]]. apply H31; auto.
    apply AxiomII'; split; try apply MKT49a; eauto.
Qed.

(* 实数 数列的上界 *)
Definition R_UP f r := r ∈ Ｒ /\ (∀ n, n ∈ ω -> f[n] = r \/ f[n] < r).

(* 定义 实数中数列的最小上界 *)
Definition R_miniUP f r := R_UP f r
  /\ (∀ r1, r1 ∈ Ｒ -> r1 < r -> ∃ n, n ∈ ω /\ r1 < f[n]).

(* 引理: 弱化的完备性, 实数域中严格单增有上界的正有理数列有最小上界. *)
Lemma R_Complete_Lemma1 : ∀ f r, R_RatSeq f -> (∀ n, n ∈ ω -> R0 < f[n])
  -> R_strictly_monoIncrease f -> R_UP f r -> ∃ r1, R_miniUP f r1.
Proof.
  Open Scope q'_scope.
  destruct NPAUF. intros. pose proof H1.
  apply Q'_RatSeq_and_R_RatSeq in H5 as [h[]]; auto. pose proof Q'0_in_Q'_Arch.
  assert (∀ n, n ∈ ω -> h[n] ∈ Q'_Q).
  { intros. destruct H5 as [H5[]]. rewrite <-H9 in H8.
    apply Property_Value,Property_ran,H10 in H8; auto. }
  assert (∀ n, n ∈ ω -> h[n] ∈ Q'_Arch).
  { intros. apply Q'_Q_subset_Q'_Arch; auto. }
  assert (∀ n, n ∈ ω -> Q'0 < h[n]).
  { intros. pose proof H10. apply H2 in H10. unfold R0 in H10.
    rewrite H6 in H10; auto. apply R_Ord_Instantiate in H10 as []; auto. }
  pose proof H5. apply RatSeq_and_NatSeq in H11 as [A[B[H11[H12[]]]]]; auto.
  assert (∀ n, n ∈ ω -> f[n] ∈ Ｑ).
  { destruct H1 as [H1[]]. intros. rewrite <-H15 in H17.
    apply Property_Value,Property_ran,H16 in H17; auto. }
  assert (∀ n, n ∈ ω -> f[n] ∈ Ｒ).
  { intros. apply Q_subset_R; auto. }
  destruct H4. pose proof H4. pose proof R0_in_R.
  assert (R0 < r)%r.
  { pose proof in_ω_0. pose proof H20. apply H2 in H20.
    pose proof H21. apply H17 in H21 as []. rewrite H21 in H20; auto.
    apply (R_Ord_Trans _ f[0]); auto. }
  apply Q_Density_Lemma in H18 as [x[H18[H21 _]]]; auto.
  pose proof H18. apply N_propersubset_R in H22; auto.
  assert (∀ n, n ∈ ω -> f[n] < x)%r.
  { intros. pose proof H23. apply H17 in H23 as [];
    [rewrite H23|apply (R_Ord_Trans _ r)]; auto. }
  pose proof H18. apply AxiomII in H24 as [_[x0[]]].
  pose proof H24. apply Q'_N_propersubset_Q'_Arch in H26; auto.
  assert (∀ n, n ∈ ω -> h[n] < x0).
  { intros. pose proof H27. apply H23 in H27.
    rewrite H6,H25 in H27; auto.
    apply R_Ord_Instantiate in H27 as []; auto. }
  pose proof Q'1_in_Q'.
  assert (x0 / Q'1 = x0).
  { pose proof Q'0_isnot_Q'1.
    apply (Q'_Mult_Cancellation Q'1 (x0 / Q'1));
    auto; try apply Q'_Divide_in_Q'; auto;
    try apply Q'_Z_subset_Q',Q'_N_propersubset_Q'_Z; auto.
    rewrite Q'_Divide_Property3,Q'_Mult_Commutation,
    Q'_Mult_Property2; auto; try apply Q'_N_subset_Q'; auto. }
  pose proof Q'1_in_Q'_N. pose proof Q'0_isnot_Q'1.
  assert (∀ n, n ∈ ω -> (A[n] / B[n]) < (x0 / Q'1)).
  { intros. rewrite <-H14,H29; auto. }
  assert ((N' ~ N'_N) <> 0).
  { destruct N'_N_propersubset_N'. intro. elim H34.
    apply AxiomI; split; intros; auto. apply NNPP; intro.
    assert (z ∈ ((N' ~ N'_N))).
    { apply MKT4'; split; [ |apply AxiomII; split]; eauto. }
    rewrite H35 in H38. elim (@ MKT16 z); auto. }
  apply NEexE in H33 as [N0]. pose proof H33.
  apply MKT4' in H34 as []. apply AxiomII in H35 as [].
  apply (Q'_extNatSeq_Property5 _ _ N0) in H32; auto; [ |apply H13]; auto.
  set (a0 := ((Q'_extNatSeq A)[N0] / (Q'_extNatSeq B)[N0])).
  assert (∀ n, n ∈ ω -> h[n] < a0).
  { intros. rewrite H14; auto.
    rewrite Q'_NatSeq_equ_Finite_extNatSeq,(Q'_NatSeq_equ_Finite_extNatSeq B);
    auto. apply Q'_extNatSeq_Property4; auto. apply H13; auto. intros.
    rewrite <-H14,<-H14; auto. apply H3 in H40; auto.
    rewrite H6,H6 in H40; auto. apply R_Ord_Instantiate in H40 as []; auto.
    apply Fn_in_N'; auto. apply N'_Infty; auto. apply Fn_in_N'_N; auto. }
  pose proof H11; pose proof H12.
  apply Q'_extNatSeq_is_Function in H38 as [H38[]];
  apply Q'_extNatSeq_is_Function in H39 as [H39[]]; auto.
  assert ((Q'_extNatSeq A)[N0] ∈ Q').
  { apply Q'_Z'_propersubset_Q',Q'_N'_propersubset_Q'_Z',H41,
    (@ Property_ran N0),Property_Value; auto. rewrite H40; auto. }
  assert ((Q'_extNatSeq B)[N0] ∈ Q').
  { apply Q'_Z'_propersubset_Q',Q'_N'_propersubset_Q'_Z',H43,
    (@ Property_ran N0),Property_Value; auto. rewrite H42; auto. }
  assert (a0 ∈ Q').
  { apply Q'_Divide_in_Q'; auto. apply Q'_extNatSeq_Property3; auto.
    apply Q'0_in_Q'_N; auto. apply H13; auto. }
  assert (Q'0 < a0).
  { pose proof in_ω_0. pose proof H47. apply H10 in H47.
    apply H37 in H48. apply (Q'_Ord_Trans _ h[0]); auto.
    apply Q'0_in_Q'; auto. apply Q'_Q_subset_Q',H8; auto. }
  assert (a0 ∈ Q'_Arch).
  { apply AxiomII; repeat split; eauto. exists x0.
    apply mt_Q'0_Q'Abs in H47; auto. rewrite H47.
    rewrite H29 in H32. split; auto. }
  set (a := (\[a0\])%r).
  assert (a ∈ Ｒ). { apply R_Instantiate2; auto. }
  exists a. repeat split; intros; auto.
  - pose proof H50. apply H37 in H50.
    apply Q'_Ord_to_R_Ord in H50; auto. rewrite <-H6 in H50; auto.
  - apply NNPP; intro. apply Q_Density in H51 as [q[H51[]]]; auto.
    assert (∀ n, n ∈ ω -> f[n] < q)%r.
    { intros. assert (f[n] ∈ Ｒ /\ r1 ∈ Ｒ) as []; auto.
      apply (R_Ord_Tri _ r1) in H56 as [H56|[]];
      try rewrite H56; auto. apply (R_Ord_Trans _ r1); auto.
      apply Q_subset_R; auto. elim H52; eauto. }
    assert (R0 < q)%r.
    { pose proof in_ω_0. pose proof H56. apply H2 in H56.
      pose proof H57. apply H55 in H57.
      apply (R_Ord_Trans _ f[0]); auto. apply Q_subset_R; auto. }
    pose proof H51. apply AxiomII in H57 as [H57[q0[]]].
    assert (Q'0 < q0).
    { rewrite H59 in H56. apply R_Ord_Instantiate in H56 as []; auto.
      apply Q'_Q_subset_Q'_Arch; auto. }
    pose proof H58. apply RatSeq_and_NatSeq_Lemma in H61 as [d[[_[H61 _]]_]];
    auto. apply AxiomII in H61 as [H61[H62[H63[c[]]]]].
    assert ((∀ n, n ∈ ω -> (A[n] / B[n]) < (c / d))).
    { intros. pose proof H66. apply H55 in H66. rewrite H6,H59 in H66; auto.
      apply R_Ord_Instantiate in H66 as [H66 _]; auto;
      try apply Q'_Q_subset_Q'_Arch; auto. rewrite <-H14,<-H65; auto. }
    apply (Q'_extNatSeq_Property5 A B N0 c d) in H66; auto; [ |apply H13]; auto.
    rewrite <-H65 in H66. replace ((Q'_extNatSeq A)[N0] / (Q'_extNatSeq B)[N0])
    with a0 in H66; auto. apply Q'_Ord_to_R_Ord in H66; auto;
    [ |apply Q'_Q_subset_Q'_Arch]; auto. rewrite <-H59 in H66.
    replace (\[a0\])%r with a in H66; auto. apply Q_subset_R in H51; auto.
    elim (R_Ord_irReflex q q); auto. destruct H66. rewrite H66 in H54; auto.
    apply (R_Ord_Trans _ a); auto.
  Close Scope q'_scope.
Qed.

(* 引理: 弱化的完备性, 严格单增有上界的有理数列有最小上界. *)
Lemma R_Complete_Lemma2 : ∀ f r, R_RatSeq f -> R_strictly_monoIncrease f
  -> R_UP f r -> ∃ r1, R_miniUP f r1.
Proof.
  destruct NPAUF. intros. destruct H1 as [H1[]].
  assert (∀ n, n ∈ ω -> f[n] ∈ Ｑ).
  { intros. rewrite <-H4 in H6.
    apply Property_Value,Property_ran in H6; auto. }
  assert (∀ n, n ∈ ω -> f[n] ∈ Ｒ).
  { intros. apply Q_subset_R; auto. }
  pose proof in_ω_0. apply H7 in H8. pose proof R0_in_R.
  assert (R0 ∈ Ｒ /\ f[0] ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri _ f[0]) in H10 as []; auto; clear H11.
  - assert (∀ n, n ∈ ω -> R0 < f[n]).
    { intros. pose proof in_ω_0.
      assert (Ordinal 0 /\ Ordinal n) as [].
      { apply AxiomII in H11 as [H11[]]. apply AxiomII in H12 as [H12[]]; auto. }
      apply  (@ MKT110 0 n) in H13 as [H13|[]]; try rewrite <-H13; auto; clear H14.
      - apply H2 in H13; auto. apply (R_Ord_Trans _ f[0]); auto.
      - elim (@ MKT16 n); auto. }
    apply (R_Complete_Lemma1 f r); auto. split; auto.
  - set (a := f[0] + |(f[0])|).
    assert (a ∈ Ｒ). { apply R_Plus_in_R; [ |apply RAbs_in_R]; auto. }
    assert (R0 = a).
    { destruct H10. apply lt_R0_RAbs in H10; auto.
      unfold a. rewrite H10. symmetry. apply R_Minus_Plus; auto.
      apply R_Minus_in_R; auto. symmetry in H10. pose proof H10.
      apply eq_R0_RAbs in H10; auto. unfold a.
      rewrite H10,H12,R_Plus_Property; auto. }
    set (b := |(f[0])| + R1). pose proof R1_in_R. pose proof R0_lt_R1.
    assert (b ∈ Ｒ). { apply R_Plus_in_R; [apply RAbs_in_R| ]; auto. }
    set (h := \{\ λ u v, u ∈ ω /\ v = f[u] + b \}\).
    assert (R_RatSeq h) as [H16[]].
    { assert (Function h).
      { split; unfold Relation; intros. apply AxiomII in H16 as [_[x[y[]]]];
        eauto. apply AxiomII' in H16 as [_[]]. apply AxiomII' in H17 as [_[]].
        rewrite H18,H19; auto. }
      split; auto. split; [(apply AxiomI; split)|unfold Included]; intros.
      - apply AxiomII in H17 as [_[]]. apply AxiomII' in H17; tauto.
      - apply AxiomII; split; eauto. exists (f[z] + b).
        pose proof H15. apply (R_Plus_in_R f[z] b) in H18; auto.
        apply AxiomII'; split; [apply MKT49a| ]; eauto.
      - apply AxiomII in H17 as [H17[]]. apply AxiomII' in H18 as [_[]].
        rewrite H19. apply Q_Plus_in_Q; auto. pose proof R1_in_Q.
        apply Q_Plus_in_Q; auto. destruct H10. apply lt_R0_RAbs in H10; auto.
        rewrite H10. apply Q_Minus_in_Q; auto. apply R0_in_Q; auto.
        pose proof in_ω_0; auto. symmetry in H10. apply eq_R0_RAbs in H10; auto.
        rewrite H10. apply R0_in_Q; auto. }
    assert (∀ n, n ∈ ω -> h[n] = f[n] + b).
    { intros. rewrite <-H17 in H19.
      apply Property_Value,AxiomII' in H19 as [_[]]; auto. }
    assert (R_strictly_monoIncrease h).
    { unfold R_strictly_monoIncrease. intros. rewrite H19,H19; auto.
      rewrite R_Plus_Commutation,(R_Plus_Commutation _ b); auto.
      apply R_Plus_PrOrder; auto. }
    assert (∀ n, n ∈ ω -> h[n] ∈ Ｑ).
    { intros. rewrite <-H17 in H21.
      apply Property_Value,Property_ran,H18 in H21; auto. }
    assert (∀ n, n ∈ ω -> h[n] ∈ Ｒ).
    { intros. apply Q_subset_R; auto. }
    assert (R0 < h[0]).
    { pose proof in_ω_0. rewrite H19; auto. unfold b.
      rewrite <-R_Plus_Association; try apply RAbs_in_R; auto.
      replace (f[0] + |(f[0])|) with a; auto.
      rewrite <-H12,R_Plus_Commutation,R_Plus_Property; auto. }
    assert (∀ n, n ∈ ω -> R0 < h[n]).
    { intros. pose proof in_ω_0.
      assert (Ordinal 0 /\ Ordinal n) as [].
      { apply AxiomII in H24 as [_[]].
        apply AxiomII in H25 as [_[]]; auto. }
      apply (@ MKT110 0 n) in H26 as [H26|[]]; try rewrite <-H26;
      auto; clear H27. apply H20 in H26; auto.
      apply (R_Ord_Trans _ h[0]); auto. elim (@ MKT16 n); auto. }
    set (r1 := r + b). assert (r1 ∈ Ｒ).
    { destruct H3. apply R_Plus_in_R; auto. }
    assert (R_UP h r1).
    { split; intros; auto. rewrite H19; auto. pose proof H26.
      destruct H3. apply H28 in H26 as []. rewrite H26; auto.
      right. unfold r1. rewrite R_Plus_Commutation,
      (R_Plus_Commutation _ b); auto. apply R_Plus_PrOrder; auto. }
    assert (∃ r2, R_miniUP h r2) as [r2[[]]].
    { apply (R_Complete_Lemma1 h r1); auto. split; auto. }
    set (r3 := r2 - b). assert (r3 ∈ Ｒ). { apply R_Minus_in_R; auto. }
    exists r3. repeat split; intros; auto.
    + pose proof H31. apply H28 in H31. rewrite H19 in H31; auto.
      destruct H31. rewrite R_Plus_Commutation in H31; auto.
      apply R_Minus_Plus in H31; auto. right.
      apply (R_Plus_PrOrder _ _ b); auto. rewrite R_Plus_Commutation; auto.
      assert (b + r3 = r2). { apply R_Minus_Plus; auto. }
      rewrite H33; auto.
    + assert (b + r3 = r2). { apply R_Minus_Plus; auto. }
      apply (R_Plus_PrOrder _ _ b) in H32; auto. rewrite H33 in H32.
      apply H29 in H32 as [x[]]; try apply R_Plus_in_R; auto.
      rewrite H19 in H34; auto. rewrite (R_Plus_Commutation _ b) in H34; auto.
      apply R_Plus_PrOrder in H34; eauto.
Qed.

(* 实数的完备性：单增有上界的实数列有最小上界. *)
Property R_Completeness : ∀ f r, R_Seq f -> R_monoIncrease f
  -> R_UP f r -> ∃ r1, R_miniUP f r1.
Proof.
  destruct NPAUF. intros. pose proof H1. destruct H1 as [H1[]].
  assert (∀ n, n ∈ ω -> f[n] ∈ Ｒ).
  { intros. rewrite <-H5 in H7.
    apply Property_Value,Property_ran,H6 in H7; auto. }
  apply R_Seq_Property2 in H4 as [[x[r1[H4[]]]]|[h[]]]; auto.
  - exists r1. assert (f[x] = r1 \/ f[x] < r1).
    { pose proof H4. apply MKT134 in H10.
      assert (x ∈ (PlusOne x)).
      { apply MKT4; right. apply MKT41; eauto. }
      pose proof H11. apply H9 in H11; auto.
      apply H2 in H12; auto. rewrite H11 in H12; auto. }
    repeat split; intros; auto.
    + assert (Ordinal x /\ Ordinal n) as [].
      { apply AxiomII in H4 as [_[]].
        apply AxiomII in H11 as [_[]]; auto. }
      apply (@ MKT110 x n) in H12 as [H12|[]]; auto; clear H13.
      apply H2 in H12; auto. destruct H10,H12; try rewrite H12; auto.
      rewrite <-H10; auto. right. apply (R_Ord_Trans _ f[x]); auto.
      rewrite <-H12; auto.
    + exists (PlusOne x). pose proof H4. apply MKT134 in H13.
      assert (x ∈ (PlusOne x)).
      { apply MKT4; right. apply MKT41; eauto. }
      apply H9 in H14; auto. rewrite H14; auto.
  - pose proof H4. apply R_subSeq_Property in H9; auto.
    destruct H4 as [H4[g0[H10[]]]]. destruct H10 as [H10[]].
    destruct H9 as [H9[]].
    assert (∀ n, n ∈ ω -> h[n] ∈ Ｒ).
    { intros. rewrite <-H15 in H17.
      apply Property_Value,Property_ran,H16 in H17; auto. }
    assert (∀ n, n ∈ ω -> h[n] = f[g0[n]]).
    { intros. rewrite <-H15 in H18.
      apply Property_Value in H18; auto. rewrite H12 in H18.
      apply AxiomII' in H18 as [_[]]. rewrite <-H12 in H19; auto. }
    assert (∀ n, n ∈ ω -> g0[n] ∈ ω).
    { intros. rewrite <-H13 in H19.
      apply Property_Value,Property_ran,H14 in H19; auto. }
    assert (R_UP h r).
    { destruct H3. split; auto. intros. rewrite H18; auto. }
    set (A n := \{ λ u, u ∈ Ｑ /\ h[n] < u /\ u < h[PlusOne n] \}).
    pose proof AxiomIX as [c[[]]].
    assert (∀ n, n ∈ ω -> (A n) ∈ dom(c)).
    { intros. pose proof H24. apply MKT134 in H25.
      assert (n ∈ (PlusOne n)).
      { apply MKT4; right. apply MKT41; eauto. }
      apply H8 in H26; auto. apply Q_Density in H26 as [q[H26[]]]; auto.
      rewrite H23. assert (Ensemble (A n)).
      { apply (MKT33 Ｒ); auto. apply R_is_Set; destruct H; auto.
        unfold Included; intros. apply AxiomII in H29 as [_[]].
        apply Q_subset_R; auto. }
      apply MKT4'; split. apply MKT19; auto. apply AxiomII; split;
      auto. intro. pose proof in_ω_0. apply MKT41 in H30; eauto.
      assert (q ∈ (A n)). { apply AxiomII; split; eauto. }
      rewrite H30 in H32. elim (@ MKT16 q); auto. }
    set (k := \{\ λ u v, u ∈ ω /\ v = c[A u] \}\).
    assert (R_RatSeq k).
    { assert (Function k).
      { split; unfold Relation; intros. apply AxiomII in H25
        as [_[x[y[]]]]; eauto. apply AxiomII' in H25 as [_[]].
        apply AxiomII' in H26 as [_[]]. rewrite H27,H28; auto. }
      split; auto. split; [(apply AxiomI; split)|
      unfold Included]; intros.
      - apply AxiomII in H26 as [_[]]. apply AxiomII' in H26; tauto.
      - apply AxiomII; split; eauto. exists (c[A z]).
        apply AxiomII'; split; [apply MKT49a| ]; eauto.
      - apply AxiomII in H26 as [H26[]].
        apply AxiomII' in H27 as [_[]]. rewrite H28.
        apply H24,H22 in H27. apply AxiomII in H27; tauto. }
    destruct H25 as [H25[]].
    assert (∀ n, n ∈ ω -> k[n] ∈ Ｒ).
    { intros. rewrite <-H26 in H28. apply Property_Value,
      Property_ran,H27,Q_subset_R in H28; auto. }
    assert (∀ n, n ∈ ω -> k[n] = c[A n]).
    { intros. rewrite <-H26 in H29.
      apply Property_Value,AxiomII' in H29; tauto. }
    assert (∀ n, n ∈ ω -> h[n] < k[n]
      /\ k[n] < h[PlusOne n]).
    { intros. pose proof H30. apply H24,H22 in H30. rewrite <-H29
      in H30; auto. apply AxiomII in H30 as [_[]]; auto. }
    assert (R_strictly_monoIncrease k).
    { unfold R_strictly_monoIncrease; intros. pose proof H31; pose proof H32.
      apply H30 in H34 as [_]. apply H30 in H35 as [H35 _]. pose proof H31.
      apply MKT134 in H36.
      assert (PlusOne m = n \/ (PlusOne m) ∈ n) as [].
      { assert (Ordinal (PlusOne m) /\ Ordinal n) as [].
        { apply AxiomII in H36 as [_[]];
          apply AxiomII in H32 as [_[]]; auto. }
        apply (@ MKT110 _ n) in H37 as [H37|[]]; auto; clear H38.
        apply MKT4 in H37 as []. elim (MKT102 m n); auto.
        apply MKT41 in H37; eauto. rewrite H37 in H33. elim (MKT101 m); auto. }
      apply (R_Ord_Trans _ h[n]); auto. rewrite <-H37; auto.
      assert (k[m] < h[n]). { apply (R_Ord_Trans _ h[PlusOne m]); auto. }
      apply (R_Ord_Trans _ h[n]); auto. }
    assert (R_UP k r).
    { destruct H20. split; intros; auto. pose proof H33.
      apply H30 in H33 as []. pose proof H34.
      apply MKT134,H32 in H34 as []. rewrite <-H34; auto.
      pose proof H36. apply MKT134 in H36. right.
      apply (R_Ord_Trans _ h[PlusOne n]); auto. }
    assert (∃ r1, R_miniUP k r1) as [a[[]]].
    { apply (R_Complete_Lemma2 k r); auto. split; auto. }
    assert (R_miniUP h a) as [[]].
    { repeat split; auto; intros.
      - pose proof H36. apply H30 in H36 as [H36 _]. pose proof H37.
        apply H34 in H37 as []. rewrite <-H37; auto. right.
        apply (R_Ord_Trans _ k[n]); auto.
      - apply H35 in H37 as [n[]]; auto. pose proof H37.
        apply H30 in H37 as [_]. pose proof H39.
        apply MKT134 in H39. exists (PlusOne n). split; auto.
        apply (R_Ord_Trans _ k[n]); auto. }
    clear H33 H34 H35 H21 H22 H23 H24. clear dependent k.
    assert (∀ n, n ∈ ω -> ∃ m w, m ∈ ω /\ w ∈ ω /\ n ∈ m /\ f[m] = h[w]).
    { intros. apply R_Seq_Property1; auto.
      split; auto. exists g0. split; auto. split; auto. }
    exists a. repeat split; auto; intros.
    + pose proof H22. apply H21 in H22 as [x[y[H22[H24[]]]]].
      apply H2 in H25; auto. pose proof H24. apply H37 in H27.
      rewrite H26 in H25. destruct H25,H27; try rewrite H25; auto.
      rewrite <-H27; auto. right.
      apply (R_Ord_Trans _ h[y]); auto.
    + apply H38 in H23 as [m[]]; auto. rewrite H18 in H24; eauto.
Qed.

