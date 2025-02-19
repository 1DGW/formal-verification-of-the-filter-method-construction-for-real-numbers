(*      This file presents the formalization of squire root and         *)
(*                 the existence of irrational numbers.                 *)
(*   It is developmented in the CoqIDE (version 8.13.2) for windows.    *)
(** square_root *)

Require Export fmcr.sequence_and_completeness.

(* 数列性质的补充 *)
Lemma N'_extSeq_Property5_Lemma : ∀ f g, Function f -> Function g
  -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
  -> Function (f ∘ g) /\ dom(f ∘ g) = ω /\ ran(f ∘ g) ⊂ ω.
Proof.
  intros. repeat split; intros.
  - unfold Relation; intros. apply AxiomII in H5 as [_[x[y[]]]]; eauto.
  - apply AxiomII' in H5 as [_[x0[]]].
    apply AxiomII' in H6 as [_[x1[]]].
    apply Property_Fun in H5,H6,H7,H8; auto.
    rewrite H7,H8,H5,H6; auto.
  - apply AxiomI; split; intros. apply AxiomII in H5 as [_[]].
    apply AxiomII' in H5 as [_[x0[]]]. apply Property_dom in H5.
    rewrite <-H2; auto. apply AxiomII; split; eauto.
    exists (f[g[z]]). rewrite <-H2 in H5. apply Property_Value
    in H5; auto. pose proof H5. apply Property_ran in H6.
    pose proof H6. apply H4 in H7. rewrite <-H1 in H7.
    apply Property_Value in H7; auto. apply AxiomII'; split; eauto.
    apply Property_dom in H5. apply Property_ran in H7.
    apply MKT49a; eauto.
  - unfold Included; intros. apply AxiomII in H5 as [H5[]].
    apply AxiomII' in H6 as [_[x0[]]].
    apply Property_ran in H7; auto.
Qed.

Property N'_extSeq_Property5 : ∀ f g m N, ω_Seq f -> ω_Seq g -> m ∈ ω
  -> (∀ n, n ∈ ω -> f[n] = g[n] + m)%ω -> N ∈ N'
  -> (N'_extSeq f)[N] = ((N'_extSeq g)[N] + (F m))%n'.
Proof.
  intros. rewrite N'_extSeq_Value,N'_extSeq_Value; auto.
  assert (ω <> 0) as HH.
  { intro. pose proof in_ω_0. rewrite H4 in H5. elim (@ MKT16 0); auto. }
  assert (Ensemble m); eauto. apply (Const_is_Function ω) in H4 as [H4[]]; auto.
  assert (ran(Const m) ⊂ ω).
  { unfold Included; intros. rewrite H6 in H7. apply MKT41 in H7; eauto.
    rewrite H7; auto. }
  assert (∀ n, n ∈ ω -> (Const m)[n] = m).
  { intros. rewrite <-H5 in H8. apply Property_Value,Property_ran in H8; auto.
    rewrite H6 in H8. apply MKT41 in H8; eauto. }
  pose proof H3. apply AxiomII in H9 as [_[h[H9[H10[]]]]].
  destruct H as [H[]]. destruct H0 as [H0[]].
  rewrite H12,FT10_Lemma,FT10_Lemma; auto; pose proof MKT138; eauto;
  [ |rewrite H15|rewrite H13]; unfold Included; auto. clear H17.
  pose proof H1. apply (F_Const_Fa F0 ω) in H17; [ |destruct NPAUF as [[_[]]_]];
  auto. rewrite <-H17. rewrite N'_Plus_Instantiate;
  try apply N'_extSeq_Property5_Lemma; auto. apply (FT8 _ _ ω).
  split. apply N'_extSeq_Property5_Lemma; auto. split.
  apply ωFun_Plus_P1; try apply N'_extSeq_Property5_Lemma; auto.
  repeat split; try apply ωFun_Plus_P1; try apply N'_extSeq_Property5_Lemma; auto.
  assert (\{ λ u, u ∈ ω /\ (f ∘ h)[u] = (((g ∘ h) + (Const m))[u])%ωfun \} = ω).
  { apply AxiomI; split; intros. apply AxiomII in H18; tauto.
    apply AxiomII; repeat split; eauto.
    rewrite ωFun_Plus_P2; try apply N'_extSeq_Property5_Lemma; auto.
    rewrite Q'_N_propersubset_Q'_N'_Lemma,Q'_N_propersubset_Q'_N'_Lemma,H8; auto.
    apply H2. rewrite <-H10 in H18.
    apply Property_Value,Property_ran in H18; auto. }
  rewrite H18. destruct NPAUF as [[_[H19 _]]_].
  apply AxiomII in H19 as [_[[]_]]; tauto.
Qed.

Property N'_extSeq_Property6: ∀ f g N, ω_Seq f -> ω_Seq g
  -> (∀ n, n ∈ ω -> f[n] = g[n] · g[n])%ω -> N ∈ N'
  -> (N'_extSeq f)[N] = ((N'_extSeq g)[N] · (N'_extSeq g)[N])%n'.
Proof.
  intros. rewrite N'_extSeq_Value,N'_extSeq_Value; auto.
  apply AxiomII in H2 as [_[h[H2[H3[]]]]].
  destruct H as [H[]]. destruct H0 as [H0[]].
  rewrite H5,FT10_Lemma,FT10_Lemma; auto; pose proof MKT138; eauto;
  [ |rewrite H8|rewrite H6]; unfold Included; auto.
  rewrite N'_Mult_Instantiate; try apply ωFun_Mult_P1;
  try apply N'_extSeq_Property5_Lemma; auto. apply (FT8 _ _ ω).
  split. apply N'_extSeq_Property5_Lemma; auto.
  split. apply ωFun_Mult_P1; apply N'_extSeq_Property5_Lemma; auto.
  repeat split; try apply ωFun_Mult_P1;
  try apply N'_extSeq_Property5_Lemma; auto.
  assert (\{ λ u, u ∈ ω /\ (f ∘ h)[u] = (((g ∘ h) · (g ∘ h))[u])%ωfun \} = ω).
  { apply AxiomI; split; intros. apply AxiomII in H11; tauto.
    apply AxiomII; repeat split; eauto.
    rewrite ωFun_Mult_P2; try apply N'_extSeq_Property5_Lemma; auto.
    rewrite Q'_N_propersubset_Q'_N'_Lemma,Q'_N_propersubset_Q'_N'_Lemma; auto. 
    apply H1. rewrite <-H3 in H11.
    apply Property_Value,Property_ran in H11; auto. }
  rewrite H11. destruct NPAUF as [[_[]]_].
  apply AxiomII in H12 as [_[[]_]]; tauto.
Qed.

Property N'_extSeq_Property7 : ∀ f m N, ω_Seq f -> m ∈ ω
  -> (∀ n, n ∈ ω -> f[n] = n + m)%ω -> N ∈ N'
  -> (N'_extSeq f)[N] = (N + (F m))%n'.
Proof.
  intros. rewrite N'_extSeq_Value; auto. destruct H as [H[]].
  apply AxiomII in H2 as [_[h[H2[H5[]]]]].
  rewrite H7,FT10_Lemma; auto; pose proof MKT138; eauto;
  [ |rewrite H3; red; auto]. clear H8. pose proof H0.
  apply (F_Const_Fa F0 ω) in H8; [ |destruct NPAUF as [[_[]]_]]; auto.
  assert (ω <> 0) as HH.
  { intro. pose proof in_ω_0. rewrite H9 in H10. elim (@ MKT16 0); auto. }
  assert (Ensemble m); eauto. apply (Const_is_Function ω) in H9 as [H9[]]; auto.
  assert (∀ n, n ∈ ω -> (Const m)[n] = m).
  { intros. rewrite <-H10 in H12. apply Property_Value,Property_ran in H12; auto.
    rewrite H11 in H12. apply MKT41 in H12; eauto. }
  assert (ran(Const m) ⊂ ω).
  { unfold Included; intros. rewrite H11 in H13.
    apply MKT41 in H13; eauto. rewrite H13; auto. }
  rewrite <-H8,N'_Plus_Instantiate; auto. apply (FT8 _ _ ω).
  split. apply N'_extSeq_Property5_Lemma; auto.
  split. apply ωFun_Plus_P1; auto.
  repeat split; try apply N'_extSeq_Property5_Lemma; try apply ωFun_Plus_P1; auto.
  assert (\{ λ u, u ∈ ω /\ (f ∘ h)[u] = ((h + Const m)[u])%ωfun \} = ω).
  { apply AxiomI; split; intros. apply AxiomII in H14; tauto.
    apply AxiomII; repeat split; eauto.
    rewrite Q'_N_propersubset_Q'_N'_Lemma,ωFun_Plus_P2; auto.
    rewrite H1,H12; auto. rewrite <-H5 in H14.
    apply Property_Value,Property_ran in H14; auto. }
  rewrite H14. destruct NPAUF as [[_[]]_].
  apply AxiomII in H15 as [_[[]_]]; tauto.
Qed.

Open Scope q'_scope.

Property Q'_extNatSeq_Property6 : ∀ f g m N, Q'_NatSeq f -> Q'_NatSeq g
  -> m ∈ Q'_N -> (∀ n, n ∈ ω -> f[n] = g[n] + m) -> N ∈ N'
  -> (Q'_extNatSeq f)[N] = (Q'_extNatSeq g)[N] + m.
Proof.
  intros. unfold Q'_extNatSeq.
  pose proof H. apply Q'_NatSeq_and_ω_Seq in H4; auto.
  pose proof H0. apply Q'_NatSeq_and_ω_Seq in H5; auto.
  destruct (N'_extSeq_is_Function (φ4⁻¹ ∘ f)).
  pose proof H4. apply N'_extSeq_ran in H8; auto.
  destruct (N'_extSeq_is_Function (φ4⁻¹ ∘ g)).
  pose proof H5. apply N'_extSeq_ran in H11; auto.
  assert (∀ n, n ∈ ω -> (φ4⁻¹ ∘ f)[n] = ((φ4⁻¹ ∘ g)[n] + (φ4⁻¹)[m])%ω).
  { intros. pose proof H12. apply H2 in H13.
    destruct φ4_is_Function as [[][]].
    assert (f[n] ∈ ran(φ4) /\ g[n] ∈ ran(φ4)) as [].
    { destruct H as [H[]]. destruct H0 as [H0[]].
      split; [apply H19|apply H21]; apply (@ Property_ran n),
      Property_Value; auto; [rewrite H18|rewrite H20]; auto. }
    assert (∀ m, m ∈ Q'_N -> (φ4⁻¹)[m] ∈ ω).
    { intros. unfold Q'_N in H20. rewrite reqdi in H20.
      apply Property_Value,Property_ran in H20; auto.
      rewrite <-deqri,H16 in H20; auto. }
    destruct H as [H[]]. destruct H0 as [H0[]].
    rewrite <-(f11vi φ4 (f[n])),<-(f11vi φ4 (g[n])),
    <-(f11vi φ4 m),<-φ4_PrPlus,
    <-(Q'_N_propersubset_Q'_N'_Lemma _ f),
    <-(Q'_N_propersubset_Q'_N'_Lemma _ g) in H13; auto.
    destruct H4 as [H4[]]. destruct H5 as [H5[]].
    apply f11inj in H13; auto;
    rewrite H16,Q'_N_propersubset_Q'_N'_Lemma; auto.
    apply ω_Plus_in_ω; auto. }
  assert ((φ4⁻¹)[m] ∈ ω).
  { destruct φ4_is_Function as [[][]]. unfold Q'_N in H1.
    rewrite reqdi in H1. apply Property_Value,Property_ran in H1; auto.
    rewrite <-deqri,H15 in H1; auto. }
  apply (N'_extSeq_Property5 _ _ _ N) in H12; auto.
  destruct φ3_is_Function as [[][]].
  rewrite Q'_N_propersubset_Q'_N'_Lemma,
  Q'_N_propersubset_Q'_N'_Lemma,H12,φ3_PrPlus; auto.
  - replace (φ3[F (φ4⁻¹)[m]]) with m; auto.
    destruct φ_is_Function as [[][]]. pose proof H13. rewrite <-H20 in H22.
    apply Property_Value,AxiomII' in H22 as [_[_]]; auto. rewrite <-H22.
    unfold φ4. rewrite MKT62,MKT62,MKT58,<-MKT62.
    replace (φ2 ∘ φ1) with φ3; auto.
    assert (m ∈ ran(φ3)).
    { pose proof φ3_ran. rewrite H23. apply Q'_N_propersubset_Q'_N'; auto. }
    rewrite Q'_N_propersubset_Q'_N'_Lemma,f11vi,f11vi; auto.
    rewrite H21,<-Q'_N_PreimageSet_N'_N; auto. pose proof H23.
    rewrite reqdi in H23. apply Property_Value,Property_ran in H23; auto.
    rewrite <-deqri in H23. apply AxiomII; repeat split; eauto.
    rewrite f11vi; auto.
  - rewrite <-H10 in H3. apply Property_Value,Property_ran in H3; auto.
  - apply Fn_in_N'; auto.
Qed.

Property Q'_extNatSeq_Property7 : ∀ f g N, Q'_NatSeq f -> Q'_NatSeq g
  -> (∀ n, n ∈ ω -> f[n] = g[n] · g[n]) -> N ∈ N'
  -> (Q'_extNatSeq f)[N] = (Q'_extNatSeq g)[N] · (Q'_extNatSeq g)[N].
Proof.
  intros. unfold Q'_extNatSeq.
  pose proof H. apply Q'_NatSeq_and_ω_Seq in H3; auto.
  pose proof H0. apply Q'_NatSeq_and_ω_Seq in H4; auto.
  destruct (N'_extSeq_is_Function (φ4⁻¹ ∘ f)).
  pose proof H3. apply N'_extSeq_ran in H7; auto.
  destruct (N'_extSeq_is_Function (φ4⁻¹ ∘ g)).
  pose proof H4. apply N'_extSeq_ran in H10; auto.
  assert (∀ n, n ∈ ω -> (φ4⁻¹ ∘ f)[n] = ((φ4⁻¹ ∘ g)[n] · (φ4⁻¹ ∘ g)[n])%ω).
  { intros. pose proof H11. apply H1 in H12.
    destruct φ4_is_Function as [[][]].
    assert (f[n] ∈ ran(φ4) /\ g[n] ∈ ran(φ4)) as [].
    { destruct H as [H[]]. destruct H0 as [H0[]].
      split; [apply H18|apply H20]; apply (@ Property_ran n),
      Property_Value; auto; [rewrite H17|rewrite H19]; auto. }
    assert (∀ m, m ∈ Q'_N -> (φ4⁻¹)[m] ∈ ω).
    { intros. unfold Q'_N in H19. rewrite reqdi in H19.
      apply Property_Value,Property_ran in H19; auto.
      rewrite <-deqri,H15 in H19; auto. }
    destruct H as [H[]]. destruct H0 as [H0[]].
    rewrite <-(f11vi φ4 (f[n])),<-(f11vi φ4 (g[n])),
    <-φ4_PrMult,<-(Q'_N_propersubset_Q'_N'_Lemma _ f),
    <-(Q'_N_propersubset_Q'_N'_Lemma _ g) in H12; auto.
    destruct H3 as [H3[]]. destruct H4 as [H4[]].
    apply f11inj in H12; auto; rewrite H15; try apply ω_Mult_in_ω;
    try rewrite Q'_N_propersubset_Q'_N'_Lemma; auto. }
  apply (N'_extSeq_Property6 _ _ N) in H11; auto.
  destruct φ3_is_Function as [[][]].
  rewrite Q'_N_propersubset_Q'_N'_Lemma,
  Q'_N_propersubset_Q'_N'_Lemma,H11,φ3_PrMult; auto;
  rewrite <-H9 in H2; apply Property_Value,Property_ran in H2; auto.
Qed.

Property Q'_extNatSeq_Property8 : ∀ f m N, Q'_NatSeq f -> m ∈ Q'_N
  -> (∀ n, n ∈ ω -> f[n] = φ4[n] + m) -> N ∈ N'
  -> (Q'_extNatSeq f)[N] = φ3[N] + m.
Proof.
  intros. unfold Q'_extNatSeq.
  pose proof H. apply Q'_NatSeq_and_ω_Seq in H3; auto.
  destruct (N'_extSeq_is_Function (φ4⁻¹ ∘ f)). pose proof H3.
  apply N'_extSeq_ran in H6; auto. destruct φ4_is_Function as [[][]].
  assert (φ4⁻¹[m] ∈ ω).
  { unfold Q'_N in H0. rewrite reqdi in H0.
    apply Property_Value,Property_ran in H0; auto.
    rewrite <-deqri,H9 in H0; auto. }
  pose proof H3. apply (N'_extSeq_Property7 _ (φ4⁻¹[m]) N) in H12; auto.
  - destruct φ3_is_Function as [[][]].
    rewrite Q'_N_propersubset_Q'_N'_Lemma,H12; auto.
    destruct φ_is_Function as [[][]]. rewrite <-H19 in H11.
    apply Property_Value,AxiomII' in H11 as [_[]]; auto.
    rewrite <-H21. unfold φ4. rewrite MKT62,MKT62,MKT58,<-MKT62.
    replace (φ2 ∘ φ1) with φ3; auto.
    assert (m ∈ ran(φ3)).
    { pose proof φ3_ran. rewrite H22. apply Q'_N_propersubset_Q'_N'; auto. }
    assert (φ3⁻¹[m] ∈ ran(φ)).
    { rewrite H20,<-Q'_N_PreimageSet_N'_N; auto. pose proof H22.
      rewrite reqdi in H23. apply Property_Value,Property_ran in H23; auto.
      rewrite <-deqri in H23. apply AxiomII; repeat split; eauto.
      rewrite f11vi; auto. }
    rewrite Q'_N_propersubset_Q'_N'_Lemma,f11vi; auto.
    rewrite φ3_PrPlus,f11vi; auto. rewrite H20 in H23.
    apply N'_N_subset_N'; auto.
  - intros. destruct H as [H[]].
    rewrite Q'_N_propersubset_Q'_N'_Lemma,H1; auto.
    assert (φ4[n] + m = φ4[(n + φ4⁻¹[m])%ω]). { rewrite φ4_PrPlus,f11vi; auto. }
    rewrite H16,f11iv; auto. rewrite H9. apply ω_Plus_in_ω; auto.
Qed.

Property Q'_extNatSeq_Property9 : ∀ f g q N, Q'_NatSeq f -> Q'_NatSeq g
  -> (∀ n, g[n] <> Q'0) -> q ∈ Q'_Arch -> (∀ n, n ∈ ω -> f[n]/g[n] < q)
  -> N ∈ N' -> ((Q'_extNatSeq f)[N] / (Q'_extNatSeq g)[N]) ∈ Q'_Arch.
Proof.
  intros. set (B := (Q'_extNatSeq f)[N] / (Q'_extNatSeq g)[N]).
  assert (B ∈ Q').
  { pose proof H. pose proof H0.
    apply Q'_extNatSeq_is_Function in H5 as [H5[]]; auto.
    apply Q'_extNatSeq_is_Function in H6 as [H6[]]; auto.
    pose proof H4; pose proof H4. rewrite <-H7 in H11.
    rewrite <-H9 in H12. apply Property_Value,Property_ran in H11,H12; auto.
    apply Q'_Divide_in_Q'; auto; try apply Q'_N'_propersubset_Q'; auto.
    apply Q'_extNatSeq_Property3; auto. apply Q'0_in_Q'_N; auto. }
  assert (∀ n, n ∈ ω -> f[n]/g[n] ∈ Q').
  { intros. destruct H as [H[]]. destruct H0 as [H0[]].
    pose proof H6. rewrite <-H7 in H6. rewrite <-H9 in H11.
    apply Property_Value,Property_ran in H6,H11; auto.
    apply Q'_Divide_in_Q'; try apply Q'_N_subset_Q'; auto. }
  pose proof H2. apply AxiomII in H7 as [_[H7[k[]]]].
  assert (∀ n, n ∈ ω -> f[n]/g[n] < k).
  { pose proof H7. apply Self_le_Q'Abs in H10; auto.
    destruct H9,H10; intros. rewrite <-H9,<-H10; auto.
    rewrite <-H9. apply (Q'_Ord_Trans _ q); auto with Q'.
    rewrite <-H10 in H9. apply (Q'_Ord_Trans _ q); auto.
    apply Q'_N_subset_Q'; auto. apply (Q'_Ord_Trans q) in H9; auto with Q'.
    apply (Q'_Ord_Trans _ q); auto. apply Q'_N_subset_Q'; auto.
    apply Q'_N_subset_Q'; auto. }
  assert (k = k / Q'1).
  { rewrite Q'_Divide_Property2; try apply Q'_N_subset_Q'; auto. }
  rewrite H11 in H10. apply (Q'_extNatSeq_Property5 f g N) in H10;
  try apply Q'1_in_Q'_N; try (intro; apply Q'0_isnot_Q'1); auto.
  rewrite <-H11 in H10. apply AxiomII; repeat split; eauto.
  assert ((Q'_extNatSeq g)[N] ∈ Q'_N').
  { pose proof H0. apply Q'_extNatSeq_is_Function in H0 as [H0[]]; auto.
    pose proof H4. rewrite <-H13 in H15.
    apply Property_Value,Property_ran,H14 in H15; auto. }
  assert ((Q'_extNatSeq g)[N] <> Q'0).
  { apply Q'_extNatSeq_Property3; auto. apply Q'0_in_Q'_N; auto. }
  pose proof H12. apply Q'_N'_propersubset_Q' in H12; auto.
  apply Q'_N'_Q'0_is_FirstMember in H14; auto.
  assert ((Q'_extNatSeq f)[N] ∈ Q'_N').
  { pose proof H. apply Q'_extNatSeq_is_Function in H as [H[]]; auto.
    pose proof H4. rewrite <-H16 in H18.
    apply Property_Value,Property_ran,H17 in H18; auto. }
  exists k. destruct (classic ((Q'_extNatSeq f)[N] = Q'0)).
  - assert (B = Q'0).
    { unfold B. rewrite H16.
      apply (Q'_Mult_Cancellation (Q'_extNatSeq g)[N]); auto with Q'.
      rewrite Q'_Divide_Property3,Q'_Mult_Property1; auto with Q'. }
    unfold B in H17. rewrite H17 in H10. apply eq_Q'0_Q'Abs in H17; auto.
    unfold B. rewrite H17; auto.
  - pose proof H15. apply Q'_N'_propersubset_Q' in H15; auto.
    apply Q'_N'_Q'0_is_FirstMember in H17; auto.
    assert (Q'0 < B).
    { apply (Q'_Mult_PrOrder _ _ (Q'_extNatSeq g)[N]); auto with Q'.
      unfold B. rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto. }
    apply mt_Q'0_Q'Abs in H18; auto. rewrite H18; auto.
Qed.

Property Q'_extNatSeq_Property10 : ∀ f g q N, Q'_NatSeq f -> Q'_NatSeq g
  -> (∀ n, g[n] <> Q'0) -> q ∈ Q'_Arch -> (∀ n, n ∈ ω -> f[n]/g[n] < q)
  -> N ∈ N' -> (\[((Q'_extNatSeq f)[N] / (Q'_extNatSeq g)[N])%q'\] = \[q\]
    \/ \[((Q'_extNatSeq f)[N] / (Q'_extNatSeq g)[N])%q'\] < \[q\])%r.
Proof.
  intros. set (B := (Q'_extNatSeq f)[N] / (Q'_extNatSeq g)[N]).
  assert (B ∈ Q'_Arch). { eapply Q'_extNatSeq_Property9; eauto. }
  pose proof H5. apply Q'_Arch_subset_Q' in H6; auto.
  set (Br := (\[B\])%r). set (qr := (\[q\])%r).
  assert (Br ∈ Ｒ /\ qr ∈ Ｒ) as []. { split; apply R_Instantiate2; auto. }
  destruct (R_Ord_Tri Br qr) as [H9|[|]]; auto.
  apply Q_Density in H9 as [xr[H9[]]]; auto.
  apply AxiomII in H9 as [_[x[]]]. pose proof H9.
  apply Q'_Q_subset_Q'_Arch in H13; auto. rewrite H12 in H10,H11.
  apply R_Ord_Instantiate in H10 as [H10 _]; auto.
  apply R_Ord_Instantiate in H11 as [H11 _]; auto.
  assert (∀ n, n ∈ ω -> f[n]/g[n] ∈ Q').
  { intros. destruct H as [H[]]. destruct H0 as [H0[]].
    pose proof H14. rewrite <-H15 in H14. rewrite <-H17 in H19.
    apply Property_Value,Property_ran in H14,H19; auto.
    apply Q'_Divide_in_Q'; try apply Q'_N_subset_Q'; auto. }
  assert (∀ n, n ∈ ω -> f[n]/g[n] < x).
  { intros. apply (Q'_Ord_Trans _ q); auto; apply Q'_Arch_subset_Q'; auto. }
  assert (∀ n, n ∈ ω -> Q'0 = f[n]/g[n] \/ Q'0 < f[n]/g[n]).
  { intros. destruct H as [H[]]. destruct H0 as [H0[]].
    pose proof H16. rewrite <-H17 in H16. rewrite <-H19 in H21.
    apply Property_Value,Property_ran in H16,H21; auto.
    apply H18 in H16; apply H20 in H21. pose proof H16; pose proof H21.
    apply Q'_N_subset_Q' in H22,H23; auto.
    destruct (classic (f[n] = Q'0)).
    - left. rewrite H24. apply (Q'_Mult_Cancellation g[n]); auto with Q'.
      rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto with Q'.
    - assert (f[n] ∈ (Q'_N ~ [Q'0])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. apply MKT41 in H25; eauto with Q'. }
      assert (g[n] ∈ (Q'_N ~ [Q'0])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. apply MKT41 in H26; eauto with Q'. elim (H1 n); auto. }
      apply Q'_N_Q'0_is_FirstMember in H25,H26; auto. right.
      apply (Q'_Mult_PrOrder _ _ g[n]); auto with Q'.
      rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto. }
  assert (Q'0 < x).
  { pose proof in_ω_0. pose proof H17. apply H15 in H17.
    pose proof H18. apply H16 in H18 as []. rewrite H18; auto.
    apply (Q'_Ord_Trans Q'0) in H17; auto with Q'.
    apply Q'_Q_subset_Q'; auto. }
  pose proof H9. apply RatSeq_and_NatSeq_Lemma in H18 as [b[[H18[H19 _]]_]]; auto.
  apply AxiomII in H19 as [_[H19[H20[a[]]]]]. rewrite H22 in H15.
  apply (Q'_extNatSeq_Property5 f g N) in H15; auto. rewrite <-H22 in H15.
  apply (Q'_Ord_Trans x) in H15; auto; try apply Q'_Q_subset_Q'; auto.
  elim (Q'_Ord_irReflex x x); auto; apply Q'_Q_subset_Q'; auto.
Qed.

(* *Q中的正分数列大于某一正分数, 无穷项也大于该正分数 *)
Property Q'_extNatSeq_Property11 : ∀ f g N a b, Q'_NatSeq f -> Q'_NatSeq g
  -> (∀ n, g[n] <> Q'0) -> N ∈ N' -> a ∈ Q'_N -> b ∈ Q'_N -> b <> Q'0
  -> (∀ n, n ∈ ω -> a/b < f[n]/g[n])
  -> a/b < (Q'_extNatSeq f)[N] / (Q'_extNatSeq g)[N].
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
    apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. pose proof Q'0_in_Q'. apply MKT41 in H15; eauto. elim (H1 n); auto. }
  destruct (Q'_extNatSeq_is_Function f) as [H16[]]; auto.
  destruct (Q'_extNatSeq_is_Function g) as [H18[]]; auto.
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
    apply AxiomII; split; eauto. exists (a · g[z]).
    apply AxiomII'; split; auto. pose proof H3.
    apply (Q'_N_Mult_in_Q'_N a g[z]) in H25; auto.
    apply MKT49a; eauto. unfold Included; intros.
    apply AxiomII in H24 as [H24[]]. apply AxiomII' in H25 as [H25[]].
    rewrite H27. apply Q'_N_Mult_in_Q'_N; auto. }
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
  assert (∀ n, n ∈ ω -> h[n] < k[n]).
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
  { apply H17,(@ Property_ran N),Property_Value; try rewrite H15; auto. }
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

Property Q'_extNatSeq_Property12: ∀ f g q qm N, Q'_NatSeq f -> Q'_NatSeq g
  -> (∀ n, g[n] <> Q'0) -> q ∈ Q'_Arch -> qm ∈ Q'_Arch
  -> (∀ n, n ∈ ω -> q < f[n]/g[n]) -> (∀ n, n ∈ ω -> f[n]/g[n] < qm)
  -> N ∈ N' -> (\[q\] = \[((Q'_extNatSeq f)[N] / (Q'_extNatSeq g)[N])%q'\]
    \/ \[q\] < \[((Q'_extNatSeq f)[N] / (Q'_extNatSeq g)[N])%q'\])%r.
Proof.
  intros. set (B := (Q'_extNatSeq f)[N] / (Q'_extNatSeq g)[N]).
  assert (B ∈ Q'_Arch). { eapply Q'_extNatSeq_Property9; eauto. }
  pose proof H7. apply Q'_Arch_subset_Q' in H8; auto.
  set (Br := (\[B\])%r). set (qr := (\[q\])%r).
  assert (Br ∈ Ｒ /\ qr ∈ Ｒ) as []. { split; apply R_Instantiate2; auto. }
  destruct (R_Ord_Tri Br qr) as [H11|[|]]; auto.
  apply Q_Density in H11 as [xr[H11[]]]; auto.
  apply AxiomII in H11 as [_[x[]]]. pose proof H11.
  apply Q'_Q_subset_Q'_Arch in H15; auto. rewrite H14 in H12,H13.
  apply R_Ord_Instantiate in H12 as [H12 _]; auto.
  apply R_Ord_Instantiate in H13 as [H13 _]; auto.
  assert (∀ n, n ∈ ω -> f[n]/g[n] ∈ Q').
  { intros. destruct H as [H[]]. destruct H0 as [H0[]].
    pose proof H16. rewrite <-H17 in H16. rewrite <-H19 in H21.
    apply Property_Value,Property_ran in H16,H21; auto.
    apply Q'_Divide_in_Q'; try apply Q'_N_subset_Q'; auto. }
  assert (∀ n, n ∈ ω -> x < f[n]/g[n]).
  { intros. apply (Q'_Ord_Trans _ q); auto; apply Q'_Arch_subset_Q'; auto. }
  assert (∀ n, n ∈ ω -> Q'0 = f[n]/g[n] \/ Q'0 < f[n]/g[n]).
  { intros. destruct H as [H[]]. destruct H0 as [H0[]].
    pose proof H18. rewrite <-H19 in H18. rewrite <-H21 in H23.
    apply Property_Value,Property_ran in H18,H23; auto.
    apply H20 in H18; apply H22 in H23. pose proof H18; pose proof H23.
    apply Q'_N_subset_Q' in H24,H25; auto.
    destruct (classic (f[n] = Q'0)).
    - left. rewrite H26. apply (Q'_Mult_Cancellation g[n]); auto with Q'.
      rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto with Q'.
    - assert (f[n] ∈ (Q'_N ~ [Q'0])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. apply MKT41 in H27; eauto with Q'. }
      assert (g[n] ∈ (Q'_N ~ [Q'0])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. apply MKT41 in H28; eauto with Q'. elim (H1 n); auto. }
      apply Q'_N_Q'0_is_FirstMember in H27,H28; auto. right.
      apply (Q'_Mult_PrOrder _ _ g[n]); auto with Q'.
      rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto. }
  apply Q'_Arch_subset_Q' in H15; auto.
  destruct (Q'_Ord_Tri Q'0 x) as []; auto with Q'.
  - apply RatSeq_and_NatSeq_Lemma in H11 as [b[[H11[H20 _]]_]]; auto.
    apply AxiomII in H20 as [_[H20[H21[a[]]]]]. rewrite H23 in H17.
    apply (Q'_extNatSeq_Property11 f g N) in H17; auto. rewrite <-H23 in H17.
    apply (Q'_Ord_Trans x) in H12; auto. elim (Q'_Ord_irReflex x x); auto.
  - pose proof H; pose proof H0.
    apply Q'_extNatSeq_is_Function in H20 as [H20[]]; auto.
    apply Q'_extNatSeq_is_Function in H21 as [H21[]]; auto.
    pose proof H6; pose proof H6. rewrite <-H22 in H26; rewrite <-H24 in H27.
    apply Property_Value,Property_ran in H26,H27; auto.
    apply H23 in H26; apply H25 in H27.
    apply (Q'_extNatSeq_Property3 g N) in H1; try apply Q'0_in_Q'_N; auto.
    pose proof H26; pose proof H27. apply Q'_N'_propersubset_Q' in H26,H27; auto.
    apply Q'_N'_Q'0_is_FirstMember in H29; auto.
    destruct (classic ((Q'_extNatSeq f)[N] = Q'0)).
    + assert (Q'0 = B).
      { apply (Q'_Mult_Cancellation (Q'_extNatSeq g)[N]); auto with Q'.
        unfold B. rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto. }
      rewrite H31 in H19. destruct H19;
      [apply (Q'_Ord_Trans x) in H12|rewrite H19 in H12]; auto;
      elim (Q'_Ord_irReflex x x); auto.
    + apply Q'_N'_Q'0_is_FirstMember in H30; auto.
      assert (Q'0 < B).
      { apply (Q'_Mult_PrOrder _ _ (Q'_extNatSeq g)[N]); auto with Q'.
        unfold B. rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto. }
      assert (x < B).
      { destruct H19; [apply (Q'_Ord_Trans _ Q'0)|rewrite <-H19]; auto with Q'. }
      apply (Q'_Ord_Trans x) in H12; auto. elim (Q'_Ord_irReflex x x); auto.
Qed.

(* *Q_Z中, 若u<v, 则u+1<=v *)
Lemma Square_Root_Lemma1 : ∀ u v, u ∈ Q'_Z -> v ∈ Q'_Z -> u < v
  -> u + Q'1 < v \/ u + Q'1 = v.
Proof.
  intros. pose proof H; pose proof H0. apply Q'_Z_subset_Q' in H2,H3; auto.
  pose proof H3. apply (Q'_Ord_Tri (u + Q'1)) in H4 as [H4|[|]]; auto with Q'.
  assert ((v - u) < Q'1).
  { apply (Q'_Plus_PrOrder _ _ u); auto with Q'.
    rewrite <-Q'_Mix_Association1,(Q'_Plus_Commutation u),
    Q'_Mix_Association1,Q'_Minus_Property1,Q'_Plus_Property; auto. }
  assert (Q'0 < (v - u)).
  { apply (Q'_Plus_PrOrder _ _ u); auto with Q'.
    rewrite Q'_Plus_Property,<-Q'_Mix_Association1,(Q'_Plus_Commutation u),
    Q'_Mix_Association1,Q'_Minus_Property1,Q'_Plus_Property; auto. }
  assert ((v - u) ∈ Q'_Z). { apply Q'_Z_Minus_in_Q'_Z; auto. }
  apply AxiomII in H7 as [H7[z[]]]. rewrite H9 in H5,H6.
  rewrite Q'1_Property in H5; auto. rewrite Q'0_Property in H6; auto.
  pose proof H8. apply Z'_Z_subset_Z' in H10; auto.
  apply Q'_Ord_Instantiate in H5,H6; auto with Z'.
  rewrite Z'_Mult_Property2,Z'_Mult_Property2 in H5; auto with Z'.
  rewrite Z'_Mult_Property2,Z'_Mult_Commutation,Z'_Mult_Property2 in H6;
  auto with Z'. pose proof H6. apply Z'_otherPropertys7 in H6 as []; auto.
  - apply (Z'_Ord_Trans z) in H6; auto with Z'.
    elim (Z'_Ord_irReflex z z); auto.
  - rewrite H6 in H5. elim (Z'_Ord_irReflex z z); auto.
Qed.

(* *Q中有上界的自然数集有最大值 *)
Lemma Square_Root_Lemma2 : ∀ A, A <> Φ -> A ⊂ Q'_N
  -> (∃ q, q ∈ Q'_Arch /\ (∀ a, a ∈ A -> a = q \/ a < q))
  -> (∃! m, m ∈ A /\ (∀ a, a ∈ A -> a = m \/ a < m)).
Proof.
  intros. destruct H1 as [q[]]. apply NEexE in H as [].
  set (D := \{ λ u, u ∈ Q'_N /\ (∀ a, a ∈ A -> a < u) \}).
  assert (D <> Φ).
  { assert (Q'0 = q \/ Q'0 < q).
    { pose proof H. apply H2 in H3. destruct (classic (x = Q'0)).
      rewrite <-H4; auto. assert (x ∈ (Q'_N ~ [Q'0])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. apply MKT41 in H5; eauto with Q'. }
      apply Q'_N_Q'0_is_FirstMember in H5; auto. destruct H3.
      rewrite <-H3; auto. apply (Q'_Ord_Trans _ _ q) in H5; auto with Q'.
      apply Q'_N_subset_Q'; auto. apply Q'_Arch_subset_Q'; auto. }
    assert (|q| = q).
    { destruct H3. rewrite <-H3. apply eq_Q'0_Q'Abs; auto with Q'.
      apply mt_Q'0_Q'Abs; auto. apply Q'_Arch_subset_Q'; auto. }
    pose proof H1. apply AxiomII in H5 as [_[H5[n[]]]].
    pose proof H6. apply Q'_N_subset_Q' in H8; auto. rewrite H4 in H7.
    assert (q < (n + Q'1)).
    { replace q with (q + Q'0). destruct H7. rewrite <-H7.
      apply Q'_Plus_PrOrder; auto with Q'.
      apply (Q'_Ord_Trans _ (n + Q'0)); auto with Q'.
      rewrite Q'_Plus_Property,Q'_Plus_Property; auto.
      apply Q'_Plus_PrOrder; auto with Q'. apply Q'_Plus_Property; auto. }
    assert ((n + Q'1) ∈ D).
    { apply AxiomII; repeat split; eauto with Q'.
      apply Q'_N_Plus_in_Q'_N; auto. apply Q'1_in_Q'_N; auto. intros.
      pose proof H10. apply H2 in H10 as []. rewrite H10; auto.
      apply (Q'_Ord_Trans a q); auto with Q'.
      apply H0,Q'_N_subset_Q' in H11; auto. } intro.
    rewrite H11 in H10. elim (@ MKT16 (n + Q'1)); auto. }
  assert (D ⊂ Q'_N). { unfold Included; intros. apply AxiomII in H4; tauto. }
  pose proof H3. apply (wosub Q'_N Q'_Ord D) in H5 as [d[]];
  try apply Q'_Ord_WellOrder_Q'_N; auto. pose proof H5.
  apply AxiomII in H7 as [_[]].
  assert ((d - Q'1) ∈ Q'_Z).
  { apply Q'_Z_Minus_in_Q'_Z; auto. apply Q'_N_propersubset_Q'_Z; auto.
    apply Q'1_in_Q'_Z; auto. }
  pose proof H9. apply Q'_Z_subset_Q' in H10; auto.
  pose proof H7. apply Q'_N_subset_Q' in H11; auto.
  assert ((d - Q'1) ∉ D).
  { intro. apply H6 in H12. elim H12.
    apply (Q'_Plus_PrOrder _ _ Q'1); auto with Q'.
    rewrite <-Q'_Mix_Association1,(Q'_Plus_Commutation _ d),
    Q'_Mix_Association1,Q'_Minus_Property1; auto with Q'.
    apply Q'_Plus_PrOrder; auto with Q'. }
  assert (∃ a, a ∈ A /\ ((d - Q'1) = a \/ (d - Q'1) < a)) as [a[]].
  { apply NNPP; intro. elim H12. apply AxiomII; split; eauto.
    split; intros.
    - rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; repeat split; eauto.
      assert (Q'0 < d).
      { destruct (classic (x = Q'0)). apply H8. rewrite <-H14; auto.
        assert (x ∈ (Q'_N ~ [Q'0])).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto.
          intro. apply MKT41 in H15; eauto with Q'. }
        apply Q'_N_Q'0_is_FirstMember in H15; auto.
        apply (Q'_Ord_Trans _ x); auto with Q'. apply Q'_N_subset_Q'; auto. }
      apply Square_Root_Lemma1 in H14; auto.
      rewrite Q'_Plus_Commutation,Q'_Plus_Property in H14; auto with Q'.
      destruct H14; [(right)|left].
      + apply (Q'_Plus_PrOrder _ _ Q'1); auto with Q'.
        rewrite Q'_Plus_Property,<-Q'_Mix_Association1,
        (Q'_Plus_Commutation _ d),Q'_Mix_Association1,
        Q'_Minus_Property1,Q'_Plus_Property; auto with Q'.
      + rewrite H14,Q'_Minus_Property1; auto.
      + apply Q'0_in_Q'_Z; auto.
      + apply Q'_N_propersubset_Q'_Z; auto.
    - pose proof H14. apply H0,Q'_N_subset_Q' in H15; auto.
      pose proof H10. apply (Q'_Ord_Tri a) in H16 as [H16|[|]]; auto; elim H13;
      eauto. } exists (d - Q'1).
  assert ((d - Q'1) ∈ A /\ (∀ a0, a0 ∈ A
    -> a0 = (d - Q'1) \/ a0 < (d - Q'1))) as [].
  { split; intros.
    - destruct H14. rewrite H14; auto. pose proof H13.
      apply H8 in H15. apply H0,Q'_N_propersubset_Q'_Z in H13; auto.
      pose proof H13. apply Q'_Z_subset_Q' in H16; auto.
      apply Square_Root_Lemma1 in H14; auto.
      rewrite Q'_Plus_Commutation,<-Q'_Mix_Association1,
      (Q'_Plus_Commutation _ d),Q'_Mix_Association1,
      Q'_Minus_Property1,Q'_Plus_Property in H14; auto with Q'.
      destruct H14; [apply (Q'_Ord_Trans d) in H15; auto|
      rewrite <-H14 in H15]; elim (Q'_Ord_irReflex d d); auto.
    - pose proof H15. apply H0,Q'_N_propersubset_Q'_Z in H15; auto.
      pose proof H15. apply Q'_Z_subset_Q' in H17; auto.
      apply Q'_N_propersubset_Q'_Z in H7; auto.
      apply H8,Square_Root_Lemma1 in H16 as []; auto; [(right)|left].
      + apply (Q'_Plus_PrOrder _ _ Q'1); auto with Q'.
        rewrite <-Q'_Mix_Association1,(Q'_Plus_Commutation _ d),
        Q'_Mix_Association1,Q'_Minus_Property1,Q'_Plus_Property,
        Q'_Plus_Commutation; auto with Q'.
      + rewrite <-H16. rewrite Q'_Mix_Association1,
        Q'_Minus_Property1,Q'_Plus_Property; auto with Q'. }
  split; auto. intros m []. pose proof H17.
  apply H0,Q'_N_subset_Q' in H19; auto. pose proof H19.
  apply (Q'_Ord_Tri (d - Q'1)) in H20 as [H20|[|]]; auto.
  - apply H16 in H17 as []; auto. apply (Q'_Ord_Trans m) in H20; auto.
    elim (Q'_Ord_irReflex m m); auto.
  - apply H18 in H15 as []; auto. apply (Q'_Ord_Trans m) in H15; auto.
    elim (Q'_Ord_irReflex m m); auto.
Qed.

Lemma Square_Root_Lemma3 : ∀ n q, n ∈ Q'_N -> q ∈ Q'
  -> (n · n = q \/ (n · n) < q) -> (n = q \/ n < q).
Proof.
  intros. destruct (classic (n = Q'0)).
  - rewrite H2 in *. rewrite Q'_Mult_Property1 in H1; auto with Q'.
  - assert (n ∈ (Q'_N ~ [Q'0])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H3; eauto with Q'. }
    apply Q'_N_Q'0_is_FirstMember in H3; auto. pose proof H3.
    apply Square_Root_Lemma1 in H3; auto;
    [ |apply Q'0_in_Q'_Z|apply Q'_N_propersubset_Q'_Z]; auto.
    rewrite Q'_Plus_Commutation,Q'_Plus_Property in H3; auto with Q'.
    destruct H3.
    + destruct (Q'_Ord_Tri n q) as [H5|[|]]; auto. apply Q'_N_subset_Q'; auto.
      assert (Q'0 < (n · n)).
      { replace Q'0 with (n · Q'0).
        apply Q'_Mult_PrOrder; auto with Q'; apply Q'_N_subset_Q'; auto.
        rewrite Q'_Mult_Property1; auto. apply Q'_N_subset_Q'; auto. }
      assert (Q'0 < q).
      { destruct H1. rewrite <-H1; auto. apply Q'_N_subset_Q' in H; auto.
        apply (Q'_Ord_Trans _ (n · n)); auto with Q'. }
      apply Q'_N_subset_Q' in H; auto. apply (Q'_Mult_PrOrder _ _ n) in H5; auto.
      apply (Q'_Mult_PrOrder _ _ q) in H3; auto with Q'.
      rewrite Q'_Mult_Property2 in H3; auto.
      rewrite Q'_Mult_Commutation in H5; auto.
      apply (Q'_Ord_Trans q) in H5; auto with Q'. destruct H1. rewrite H1 in H5.
      elim (Q'_Ord_irReflex q q); auto. apply (Q'_Ord_Trans q) in H1; auto with Q'.
      elim (Q'_Ord_irReflex q q); auto.
    + rewrite <-H3 in *. rewrite Q'_Mult_Property2 in H1; auto with Q'.
Qed.

Lemma Square_Root_Lemma4 : ∀ u v, u ∈ Q' -> v ∈ Q' -> Q'0 = u \/ Q'0 < u
  -> u < v -> (u · u) < (v · v).
Proof.
  intros. destruct H1. rewrite <-H1 in H2.
  rewrite <-H1,Q'_Mult_Property1; auto with Q'. pose proof H2.
  apply (Q'_Mult_PrOrder Q'0 v v) in H2; auto with Q'.
  apply H2 in H3. rewrite Q'_Mult_Property1 in H3; auto.
  pose proof H2. apply (Q'_Ord_Trans Q'0) in H2; auto with Q'. pose proof H3.
  apply (Q'_Mult_PrOrder _ _ u) in H3; auto.
  apply (Q'_Mult_PrOrder _ _ v) in H4; auto.
  rewrite Q'_Mult_Commutation in H4; auto.
  apply (Q'_Ord_Trans (u · u)) in H4; auto with Q'.
Qed.

Lemma Square_Root_Lemma5 : ∀ u q, u ∈ Q' -> q ∈ Q' -> (u · u) < q
  -> Q'0 = u \/ Q'0 < u -> (q < Q'1 /\ u < Q'1) \/ ((Q'1 = q \/ Q'1 < q) /\ u < q).
Proof.
  intros. destruct (Q'_Ord_Tri q Q'1); auto with Q'.
  - left. split; auto. destruct (Q'_Ord_Tri u Q'1) as [H4|[|]]; auto with Q'.
    apply Square_Root_Lemma4 in H4; auto with Q'.
    rewrite Q'_Mult_Property2 in H4; auto with Q'.
    apply (Q'_Ord_Trans Q'1) in H1; auto with Q'.
    apply (Q'_Ord_Trans q) in H1; auto with Q'.
    elim (Q'_Ord_irReflex q q); auto.
    rewrite H4,Q'_Mult_Property2 in H1; auto with Q'.
    apply (Q'_Ord_Trans q) in H1; auto with Q'. elim (Q'_Ord_irReflex q q); auto.
  - right. split. destruct H3; auto.
    assert (Q'0 < q).
    { destruct H3; [apply (Q'_Ord_Trans _ Q'1)|rewrite H3]; auto with Q'. }
    destruct (Q'_Ord_Tri u q) as [H5|[|]]; auto.
    + apply Square_Root_Lemma4 in H5; auto.
      apply (Q'_Ord_Trans _ _ (q · Q'1)) in H5; auto with Q'.
      apply Q'_Mult_PrOrder in H5; auto with Q'. destruct H3;
      [apply (Q'_Ord_Trans q) in H3; auto with Q'|rewrite <-H3 in H5];
      elim (Q'_Ord_irReflex q q); auto. rewrite Q'_Mult_Property2; auto.
    + replace q with (q · Q'1) in H1. rewrite H5 in H1.
      apply Q'_Mult_PrOrder in H1; auto with Q'. destruct H3;
      [apply (Q'_Ord_Trans q) in H3; auto with Q'|rewrite <-H3 in H1];
      elim (Q'_Ord_irReflex q q); auto. rewrite Q'_Mult_Property2; auto.
Qed.

Lemma Square_Root_Lemma6 : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ
  -> ((u = v \/ u < v) /\ (v = u \/ v < u))%r <-> u = v.
Proof.
  split; intros; auto. destruct H1 as [[][]]; auto.
  apply (R_Ord_Trans u) in H2; auto. elim (R_Ord_irReflex u u); auto.
Qed.

Lemma Square_Root_Lemma7 : ∀ k, k ∈ ω -> φ4[k] ∈ Q'_N.
Proof.
  intros. destruct φ4_is_Function as [[][]].
  rewrite <-H2 in H. apply Property_Value,Property_ran in H; auto.
Qed.

Global Hint Resolve Square_Root_Lemma7 : Q'.

Module square_root_arguments.

Definition g1 := \{\ λ u v, u ∈ ω /\ v = φ4[u] + Q'1 \}\.

Fact g1_Fact1 : (Q'_NatSeq g1) /\ (∀ n, n ∈ ω -> g1[n] = φ4[n] + Q'1).
Proof.
  intros. assert (Q'_NatSeq g1).
  { repeat split; intros.
    - unfold Relation; intros.
      apply AxiomII in H as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H as [_[]]. apply AxiomII' in H0 as [_[]].
      rewrite H1,H2; auto.
    - apply AxiomI; split; intros. apply AxiomII in H as [_[]].
      apply AxiomII' in H; tauto. apply AxiomII; split; eauto.
      exists (φ4[z] + Q'1). apply AxiomII'; split; auto. apply MKT49a; eauto.
      assert ((φ4[z] + Q'1) ∈ Q'_N).
      { apply Q'_N_Plus_in_Q'_N; auto with Q'. apply Q'1_in_Q'_N; auto. } eauto.
    - unfold Included; intros. apply AxiomII in H as [_[]].
      apply AxiomII' in H as [_[]]. rewrite H0.
      apply Q'_N_Plus_in_Q'_N; auto with Q'. apply Q'1_in_Q'_N; auto. } 
  split; auto. destruct H as [H[]]. intros. rewrite <-H0 in H2.
  apply Property_Value,AxiomII' in H2; tauto.
Qed.

Fact g1_Fact2 : ∀ n, n ∈ ω -> Q'0 < g1[n].
Proof.
  intros. destruct g1_Fact1 as [_]. pose proof H. apply H0 in H1.
  destruct (classic (φ4[n] = Q'0)).
  - rewrite H2,Q'_Plus_Commutation,Q'_Plus_Property in H1; auto with Q'.
    rewrite H1; auto with Q'.
  - assert (φ4[n] ∈ (Q'_N ~ [Q'0])).
    { apply MKT4'; split; auto with Q'. apply AxiomII; split; eauto with Q'.
      intro. apply MKT41 in H3; eauto with Q'. }
    apply Q'_N_Q'0_is_FirstMember in H3; auto. pose proof Q'_N_subset_Q'.
    apply (Q'_Ord_Trans _ Q'1); auto with Q'. rewrite H1; auto with Q'.
    replace Q'1 with (Q'1 + Q'0).
    rewrite H1,(Q'_Plus_Commutation _ Q'1); auto with Q'.
    apply Q'_Plus_PrOrder; auto with Q'. rewrite Q'_Plus_Property; auto with Q'.
Qed.

Definition g2 := \{\ λ u v, u ∈ ω /\ v = g1[u] · g1[u] \}\.

Fact g2_Fact1 : (Q'_NatSeq g2) /\ (∀ n, n ∈ ω -> g2[n] = g1[n] · g1[n]).
Proof.
  intros. assert (Q'_NatSeq g2).
  { repeat split; intros.
    - unfold Relation; intros.
      apply AxiomII in H as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H as [_[]]. apply AxiomII' in H0 as [_[]].
      rewrite H1,H2; auto.
    - apply AxiomI; split; intros. apply AxiomII in H as [_[]].
      apply AxiomII' in H; tauto. apply AxiomII; split; eauto.
      exists (g1[z] · g1[z]). apply AxiomII'; split; auto. apply MKT49a; eauto.
      assert ((g1[z] · g1[z]) ∈ Q'_N).
      { destruct g1_Fact1 as [[H0[]]_]. rewrite <-H1 in H.
        apply Property_Value,Property_ran in H; auto.
        apply Q'_N_Mult_in_Q'_N; auto. } eauto.
    - unfold Included; intros. apply AxiomII in H as [_[]].
      apply AxiomII' in H as [_[]]. rewrite H0. destruct g1_Fact1 as [[H1[]]_].
      rewrite <-H2 in H. apply Property_Value,Property_ran in H; auto.
      apply Q'_N_Mult_in_Q'_N; auto. } split; auto.
  destruct H as [H[]]. intros. rewrite <-H0 in H2.
  apply Property_Value,AxiomII' in H2; tauto.
Qed.

Fact g2_Fact2 : ∀ n, n ∈ ω -> Q'0 < g2[n].
Proof.
  intros. destruct g2_Fact1 as [[H0[]]]. destruct g1_Fact1 as [[H4[]]_].
  pose proof H. apply (g1_Fact2 n) in H7; auto.
  pose proof H. rewrite <-H5 in H8.
  apply Property_Value,Property_ran,H6,Q'_N_subset_Q' in H8; auto.
  rewrite H3; auto. replace Q'0 with (g1[n] · Q'0).
  apply Q'_Mult_PrOrder; auto with Q'. rewrite Q'_Mult_Property1; auto.
Qed.

Definition A n q := \{ λ u, u ∈ Q'_N /\ (u · u) < (q · g2[n]) \}.

Fact A_Fact1 : ∀ n q, n ∈ ω -> q ∈ Q' -> Q'0 < q -> Q'0 ∈ (A n q).
Proof.
  intros. apply AxiomII; repeat split; eauto with Q'. apply Q'0_in_Q'_N.
  rewrite Q'_Mult_Property1; auto with Q'. replace Q'0 with (q · Q'0).
  destruct g2_Fact1 as [[H2[]]_]. pose proof H. apply (g2_Fact2 n) in H5; auto.
  apply Q'_Mult_PrOrder; auto with Q'. rewrite <-H3 in H.
  apply Property_Value,Property_ran in H; auto.
  apply Q'_N_subset_Q'; auto. rewrite Q'_Mult_Property1; auto.
Qed.

Fact A_Fact2 : ∀ n q, n ∈ ω -> q ∈ Q'_Arch
  -> (∃ m, m ∈ Q'_Arch /\ (∀ a, a ∈ (A n q) -> a = m \/ a < m)).
Proof.
  intros. assert ((q · g2[n]) ∈ Q'_Arch).
  { apply Q'_Arch_Mult_in_Q'_Arch; auto. destruct g2_Fact1 as [[H1[]]_].
    rewrite <-H2 in H. apply Property_Value,Property_ran in H; auto.
    apply Q'_N_propersubset_Q'_Arch; auto. }
  exists (q · g2[n]). split; auto. intros. apply AxiomII in H2 as [_[]].
  apply Square_Root_Lemma3; auto. apply Q'_Arch_subset_Q'; auto.
Qed.

Definition g3 q := \{\ λ u v, u ∈ ω /\ v ∈ (A u q)
  /\ (∀ a, a ∈ (A u q) -> a = v \/ a < v) \}\.

Fact g3_Fact : ∀ q, q ∈ Q'_Arch -> Q'0 < q -> Q'_NatSeq (g3 q).
Proof.
  intros. repeat split; intros.
  - unfold Relation; intros.
    apply AxiomII in H1 as [_[x[y[]]]]; eauto.
  - apply AxiomII' in H1 as [_[H1[]]]. apply AxiomII' in H2 as [_[H2[]]].
    assert ((A x q) ⊂ Q').
    { unfold Included; intros. apply AxiomII in H7 as [_[]].
      apply Q'_N_subset_Q'; auto. }
    destruct (Q'_Ord_Tri y z) as [H8|[|]]; auto.
    + pose proof H5. apply H4 in H9 as []; auto.
      apply (Q'_Ord_Trans y) in H9; auto. elim (Q'_Ord_irReflex y y); auto.
    + pose proof H3. apply H6 in H9 as []; auto.
      apply (Q'_Ord_Trans z) in H9; auto. elim (Q'_Ord_irReflex z z); auto.
  - apply AxiomI; split; intros. apply AxiomII in H1 as [_[]].
    apply AxiomII' in H1; tauto. apply AxiomII; split; eauto.
    assert ((A z q) ⊂ Q'_N).
    { unfold Included; intros. apply AxiomII in H2; tauto. }
    apply Square_Root_Lemma2 in H2 as [x[[]_]]; auto.
    exists x. apply AxiomII'; split; auto. apply MKT49a; eauto.
    apply NEexE; eauto. exists Q'0. apply A_Fact1; auto.
    apply Q'_Arch_subset_Q'; auto. apply A_Fact2; auto.
  - unfold Included; intros. apply AxiomII in H1 as [H1[]].
    apply AxiomII' in H2 as [_[H2[]]]. apply AxiomII in H3; tauto.
Qed.

Definition g4 q := \{\ λ u v, u ∈ ω /\ v = (g3 q)[u] · (g3 q)[u] \}\.

Fact g4_Fact : ∀ q, q ∈ Q'_Arch -> Q'0 < q -> (Q'_NatSeq (g4 q))
    /\ (∀ n, n ∈ ω -> (g4 q)[n] = (g3 q)[n] · (g3 q)[n]).
Proof.
  intros. assert (Q'_NatSeq (g4 q)).
  { repeat split; intros.
    - unfold Relation; intros.
      apply AxiomII in H1 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H1 as [_[]]. apply AxiomII' in H2 as [_[]].
      rewrite H3,H4; auto.
    - apply AxiomI; split; intros. apply AxiomII in H1 as [_[]].
      apply AxiomII' in H1; tauto. apply AxiomII; split; eauto.
      exists ((g3 q)[z] · (g3 q)[z]).
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      assert (((g3 q)[z] · (g3 q)[z]) ∈ Q'_N).
      { destruct (g3_Fact q) as [H2[]]; auto.
        rewrite <-H3 in H1. apply Property_Value,Property_ran in H1; auto.
        apply Q'_N_Mult_in_Q'_N; auto. } eauto.
    - unfold Included; intros. apply AxiomII in H1 as [_[]].
      apply AxiomII' in H1 as [_[]]. rewrite H2.
      destruct (g3_Fact q) as [H3[]]; auto. rewrite <-H4 in H1.
      apply Property_Value,Property_ran in H1; auto.
      apply Q'_N_Mult_in_Q'_N; auto. } split; auto.
  destruct H1 as [H1[]]. intros. rewrite <-H2 in H4.
  apply Property_Value,AxiomII' in H4; tauto.
Qed.

Definition g5 q := \{\ λ u v, u ∈ ω /\ v = (g3 q)[u] + (Q'1 + Q'1) \}\.

Fact g5_Fact : ∀ q, q ∈ Q'_Arch -> Q'0 < q
  -> (Q'_NatSeq (g5 q)) /\ (∀ n, n ∈ ω -> (g5 q)[n] = (g3 q)[n] + (Q'1 + Q'1)).
Proof.
  intros. assert (Q'_NatSeq (g5 q)).
  { repeat split; intros.
    - unfold Relation; intros.
      apply AxiomII in H1 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H1 as [_[]]. apply AxiomII' in H2 as [_[]].
      rewrite H3,H4; auto.
    - apply AxiomI; split; intros. apply AxiomII in H1 as [_[]].
      apply AxiomII' in H1; tauto. apply AxiomII; split; eauto.
      exists ((g3 q)[z] + (Q'1 + Q'1)).
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      assert (((g3 q)[z] + (Q'1 + Q'1)) ∈ Q'_N).
      { destruct (g3_Fact q) as [H2[]]; auto. rewrite <-H3 in H1.
        apply Property_Value,Property_ran in H1; auto.
        apply Q'_N_Plus_in_Q'_N; auto.
        apply Q'_N_Plus_in_Q'_N; try apply Q'1_in_Q'_N; auto. } eauto.
    - unfold Included; intros. apply AxiomII in H1 as [_[]].
      apply AxiomII' in H1 as [_[]]. rewrite H2.
      destruct (g3_Fact q) as [H3[]]; auto. rewrite <-H4 in H1.
      apply Property_Value,Property_ran in H1; auto.
      apply Q'_N_Plus_in_Q'_N; auto.
      apply Q'_N_Plus_in_Q'_N; try apply Q'1_in_Q'_N; auto. } split; auto.
  destruct H1 as [H1[]]. intros. rewrite <-H2 in H4.
  apply Property_Value,AxiomII' in H4; tauto.
Qed.

Definition g6 q := \{\ λ u v, u ∈ ω /\ v = (g5 q)[u] · (g5 q)[u] \}\.

Fact g6_Fact : ∀ q, q ∈ Q'_Arch -> Q'0 < q
  -> (Q'_NatSeq (g6 q)) /\ (∀ n, n ∈ ω -> (g6 q)[n] = (g5 q)[n] · (g5 q)[n]).
Proof.
  intros. assert (Q'_NatSeq (g6 q)).
  { repeat split; intros.
    - unfold Relation; intros.
      apply AxiomII in H1 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H1 as [_[]]. apply AxiomII' in H2 as [_[]].
      rewrite H3,H4; auto.
    - apply AxiomI; split; intros. apply AxiomII in H1 as [_[]].
      apply AxiomII' in H1; tauto. apply AxiomII; split; eauto.
      exists ((g5 q)[z] · (g5 q)[z]).
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      assert (((g5 q)[z] · (g5 q)[z]) ∈ Q'_N).
      { destruct (g5_Fact q) as [[H2[]]_]; auto.
        rewrite <-H3 in H1. apply Property_Value,Property_ran in H1; auto.
        apply Q'_N_Mult_in_Q'_N; auto. } eauto.
    - unfold Included; intros. apply AxiomII in H1 as [_[]].
      apply AxiomII' in H1 as [_[]]. rewrite H2.
      destruct (g5_Fact q) as [[H3[]]_]; auto.
      rewrite <-H4 in H1. apply Property_Value,Property_ran in H1; auto.
      apply Q'_N_Mult_in_Q'_N; auto. } split; auto.
  destruct H1 as [H1[]]. intros. rewrite <-H2 in H4.
  apply Property_Value,AxiomII' in H4; tauto.
Qed.

Fact g3_g1_Fact : ∀ q, q ∈ Q'_Arch -> Q'0 < q
  -> ∃ qm, qm ∈ Q'_Arch /\ (∀ n, n ∈ ω -> (g3 q)[n]/g1[n] < qm).
Proof.
  intros. destruct (g5_Fact q) as [_]; auto.
  destruct g2_Fact1 as [_]. destruct g1_Fact1 as [_].
  assert (∀ m, m ∈ ω -> Q'0 < g1[m]).
  { intros. apply (g1_Fact2 m) in H4; auto. }
  assert (∀ m, m ∈ ω -> Q'0 < g2[m]).
  { intros. apply (g2_Fact2 m) in H5; auto. }
  assert (∀ m, m ∈ ω -> g1[m] ∈ Q'_N).
  { intros. destruct g1_Fact1 as [[H7[]]_].
    rewrite <-H8 in H6. apply Property_Value,Property_ran in H6; auto. }
  assert (∀ m, m ∈ ω -> g2[m] ∈ Q'_N).
  { intros. destruct g2_Fact1 as [[H8[]]_].
    rewrite <-H9 in H7. apply Property_Value,Property_ran in H7; auto. }
  assert (∀ m, m ∈ ω -> (g3 q)[m] ∈ Q'_N).
  { intros. destruct (g3_Fact q) as [H9[]]; auto. rewrite <-H10 in H8.
    apply Property_Value,Property_ran in H8; auto. }
  pose proof Q'_N_subset_Q'. pose proof H. apply Q'_Arch_subset_Q' in H10.
  assert (∀ m, m ∈ ω -> g1[m] <> Q'0).
  { intros; intro. pose proof H11. apply H4 in H13.
    rewrite H12 in H13. elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
  assert (∀ m, m ∈ ω -> g2[m] <> Q'0).
  { intros; intro. pose proof H12. apply H5 in H14.
    rewrite H13 in H14. elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
  assert (∀ m, m ∈ ω -> Q'0 = (g3 q)[m]/g1[m] \/ Q'0 < (g3 q)[m]/g1[m]).
  { intros. destruct (classic ((g3 q)[m] = Q'0)).
    - left. rewrite H14. apply (Q'_Mult_Cancellation g1[m]); auto with Q'.
      rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto with Q'.
    - assert ((g3 q)[m] ∈ (Q'_N ~ [Q'0])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. elim H14. apply MKT41 in H15; eauto with Q'. }
      apply Q'_N_Q'0_is_FirstMember in H15; auto. right.
      apply (Q'_Mult_PrOrder _ _ g1[m]); auto with Q'.
      rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto. }
  assert (∀ m, m ∈ ω -> (g3 q)[m] / g1[m] ∈ Q').
  { intros. apply Q'_Divide_in_Q'; auto. }
  destruct (g3_Fact q) as [H15[]]; auto.
  assert (∀ m, m ∈ ω -> (((g3 q)[m] · (g3 q)[m]) / (g1[m] · g1[m])) < q).
  { intros. rewrite <-H16 in H18.
    apply Property_Value,AxiomII' in H18 as [_[H18[]]]; auto.
    apply AxiomII in H19 as [_[_]]. rewrite <-H2; auto.
    apply (Q'_Mult_PrOrder _ _ g2[m]); auto. apply Q'_Divide_in_Q'; auto with Q'.
    rewrite Q'_Divide_Property3,(Q'_Mult_Commutation _ q); auto with Q'. }
  destruct (Q'_Ord_Tri q Q'1); auto with Q'.
  - exists Q'1. split. apply Q'1_in_Q'_Arch; auto. intros. pose proof H20.
    apply H18 in H20. rewrite Q'_Frac_Square in H20; auto.
    apply Square_Root_Lemma5 in H20 as [[]|[]]; auto.
    destruct H20; [rewrite H20 in H19|apply (Q'_Ord_Trans q) in H20];
    auto with Q'; elim (Q'_Ord_irReflex q q); auto.
  - exists q. split; auto. intros. pose proof H20. apply H18 in H20.
    rewrite Q'_Frac_Square in H20; auto.
    apply Square_Root_Lemma5 in H20 as [[]|[]]; auto. 
    destruct H19; [apply (Q'_Ord_Trans q) in H19|rewrite <-H19 in H20];
    auto with Q'; elim (Q'_Ord_irReflex q q); auto.
Qed.

Fact g5_g1_Fact : ∀ q, q ∈ Q'_Arch -> Q'0 < q
  -> ∃ qm, qm ∈ Q'_Arch /\ (∀ n, n ∈ ω -> (g5 q)[n]/g1[n] < qm).
Proof.
  intros. destruct (g5_Fact q) as [_]; auto.
  destruct g2_Fact1 as [_]. destruct g1_Fact1 as [_].
  assert (∀ m, m ∈ ω -> Q'0 < g1[m]). { intros. apply (g1_Fact2 m) in H4; auto. }
  assert (∀ m, m ∈ ω -> Q'0 < g2[m]). { intros. apply (g2_Fact2 m) in H5; auto. }
  assert (∀ m, m ∈ ω -> g1[m] ∈ Q'_N).
  { intros. destruct g1_Fact1 as [[H8[]]_]. rewrite <-H7 in H6.
    apply Property_Value,Property_ran in H6; auto. }
  assert (∀ m, m ∈ ω -> g2[m] ∈ Q'_N).
  { intros. destruct g2_Fact1 as [[H8[]]_]. rewrite <-H9 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  assert (∀ m, m ∈ ω -> (g3 q)[m] ∈ Q'_N).
  { intros. destruct (g3_Fact q) as [H9[]]; auto. rewrite <-H10 in H8.
    apply Property_Value,Property_ran in H8; auto. }
  pose proof Q'_N_subset_Q'. pose proof H. apply Q'_Arch_subset_Q' in H10.
  assert (∀ m, m ∈ ω -> g1[m] <> Q'0).
  { intros; intro. pose proof H11. apply H4 in H13. rewrite H12 in H13.
    elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
  assert (∀ m, m ∈ ω -> g2[m] <> Q'0).
  { intros; intro. pose proof H12. apply H5 in H14. rewrite H13 in H14.
    elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
  assert (∀ m, m ∈ ω -> Q'0 = (g3 q)[m] / g1[m] \/ Q'0 < ((g3 q)[m] / g1[m])).
  { intros. destruct (classic ((g3 q)[m] = Q'0)).
    - left. rewrite H14. apply (Q'_Mult_Cancellation g1[m]); auto with Q'.
      rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto with Q'.
    - assert ((g3 q)[m] ∈ (Q'_N ~ [Q'0])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. elim H14. apply MKT41 in H15; eauto with Q'. }
      apply Q'_N_Q'0_is_FirstMember in H15; auto. right.
      apply (Q'_Mult_PrOrder _ _ g1[m]); auto with Q'.
      rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto. }
  assert (∀ m, m ∈ ω -> (g3 q)[m] / g1[m] ∈ Q').
  { intros. apply Q'_Divide_in_Q'; auto. }
  assert (∃ q1, q1 ∈ Q'_Arch
    /\ (∀ m, m ∈ ω -> ((g3 q)[m] / g1[m]) < q1)) as [q1[]].
  { apply g3_g1_Fact; auto. }
  assert (∃ q2, q2 ∈ Q'_Arch
    /\ ∀ m, m ∈ ω -> ((Q'1 + Q'1) / g1[m]) < q2) as [q2[]].
  { set (q2 := Q'1 + (Q'1 + Q'1)).
    assert (q2 ∈ Q'_Arch).
    { pose proof Q'1_in_Q'_Arch. apply Q'_Arch_Plus_in_Q'_Arch; auto with Q'. }
    exists q2. split; auto. intros. pose proof H17.
    apply Q'_Arch_subset_Q' in H19; auto.
    apply (Q'_Mult_PrOrder _ _ g1[m]); auto with Q'.
    rewrite Q'_Divide_Property3,(Q'_Mult_Commutation _ q2),H3; auto with Q'.
    assert (φ4[m] ∈ Q' /\ (Q'0 = φ4[m] \/ Q'0 < φ4[m])) as [].
    { destruct φ4_is_Function as [[][]]. rewrite <-H22 in H18.
      apply Property_Value,Property_ran in H18; auto. split.
      apply Q'_N_subset_Q'; auto. destruct (classic (Q'0 = φ4[m])); auto.
      right. apply Q'_N_Q'0_is_FirstMember; auto.
      apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H25; eauto with Q'. }
    rewrite Q'_Mult_Distribution,Q'_Mult_Property2; auto with Q'.
    assert (Q'0 < q2).
    { apply (Q'_Ord_Trans _ Q'1); auto with Q'. replace Q'1 with (Q'1 + Q'0).
      apply Q'_Plus_PrOrder; auto with Q'.
      apply (Q'_Ord_Trans _ Q'1); auto with Q'.
      assert ((Q'1 + Q'0) < (Q'1 + Q'1)). { apply Q'_Plus_PrOrder; auto with Q'. }
      rewrite Q'_Plus_Property in H22; auto with Q'.
      rewrite Q'_Plus_Property; auto with Q'. }
    assert (Q'0 = (q2 · φ4[m]) \/ Q'0 < (q2 · φ4[m])).
    { destruct H21. left. rewrite <-H21,Q'_Mult_Property1; auto.
      right. apply (Q'_Mult_PrOrder _ _ q2) in H21; auto with Q'.
      rewrite Q'_Mult_Property1 in H21; auto. }
    assert (Q'0 < ((q2 · φ4[m]) + Q'1)).
    { destruct H23. rewrite <-H23,Q'_Plus_Commutation,Q'_Plus_Property;
      auto with Q'. rewrite Q'_Plus_Commutation; auto with Q'.
      apply (Q'_Ord_Trans _ Q'1); auto with Q'.
      apply (Q'_Plus_PrOrder _ _ Q'1) in H23; auto with Q'.
      rewrite Q'_Plus_Property in H23; auto with Q'. }
    apply (Q'_Plus_PrOrder _ _ (Q'1 + Q'1)) in H24; auto with Q'.
    rewrite Q'_Plus_Property in H24; auto with Q'.
    rewrite (Q'_Plus_Commutation (Q'1 + Q'1)),
    (Q'_Plus_Association _ Q'1) in H24; auto with Q'. }
  exists (q1 + q2). split; auto with Q'. intros.
  rewrite H1,Q'_Divide_Distribution; auto with Q'.
  pose proof H19. apply H18 in H20.
  apply Q'_Arch_subset_Q' in H15,H17; auto.
  apply (Q'_Plus_PrOrder _ _ ((g3 q)[n] / g1[n])) in H20; auto with Q'.
  pose proof H19. apply H16 in H21. apply (Q'_Plus_PrOrder _ _ q2) in H21;
  auto with Q'. rewrite (Q'_Plus_Commutation _ q1) in H21; auto.
  apply (Q'_Ord_Trans _ (q2 + ((g3 q)[n] / g1[n]))); auto with Q'. 
  rewrite (Q'_Plus_Commutation q2); auto with Q'.
Qed.

Fact g4_g2_Fact : ∀ q n, q ∈ Q'_Arch -> Q'0 < q -> n ∈ ω
  -> (g4 q)[n]/g2[n] < q.
Proof.
  intros. destruct g2_Fact1 as [[H3[]]_]. pose proof H1.
  apply (g2_Fact2 n) in H5; auto.
  assert (g2[n] <> Q'0).
  { intro. rewrite H6 in H5.
    elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
  pose proof H1. rewrite <-H2 in H7.
  apply Property_Value,Property_ran,H4,Q'_N_subset_Q' in H7; auto.
  pose proof H. apply Q'_Arch_subset_Q' in H8; auto.
  destruct (g4_Fact q) as [[H9[]]]; auto. pose proof H1. rewrite <-H10 in H13.
  apply Property_Value,Property_ran,H11,Q'_N_subset_Q' in H13; auto.
  apply (Q'_Mult_PrOrder _ _ g2[n]); auto with Q'.
  rewrite Q'_Divide_Property3; auto. rewrite H12; auto.
  destruct (g3_Fact q) as [H14[]]; auto. rewrite <-H15 in H1.
  apply Property_Value,AxiomII' in H1 as [_[H1[H17 _]]]; auto.
  apply AxiomII in H17 as [_[]]. rewrite (Q'_Mult_Commutation _ q); auto.
Qed.

Fact g6_g2_Fact1 : ∀ q n, q ∈ Q'_Arch -> Q'0 < q -> n ∈ ω
  -> q < (g6 q)[n]/g2[n].
Proof.
  intros. destruct g2_Fact1 as [[H2[]]_]. pose proof H1.
  apply (g2_Fact2 n) in H5; auto. assert (g2[n] <> Q'0).
  { intro. rewrite H6 in H5.
    elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
  pose proof H1. rewrite <-H3 in H7.
  apply Property_Value,Property_ran,H4,Q'_N_subset_Q' in H7; auto.
  pose proof H. apply Q'_Arch_subset_Q' in H8; auto.
  pose proof H1. apply (g6_Fact q) in H9; auto. rewrite H9; auto. clear H9.
  pose proof H1. apply (g5_Fact q) in H9; auto. rewrite H9; auto. clear H9.
  destruct (g3_Fact q) as [H9[]]; auto. pose proof H1. rewrite <-H10 in H12.
  apply Property_Value,AxiomII' in H12 as [_[_[]]]; auto.
  apply AxiomII in H12 as [_[]]. pose proof H12.
  apply Q'_N_subset_Q' in H15; auto. apply (Q'_Mult_PrOrder _ _ g2[n]); auto.
  apply Q'_Divide_in_Q'; auto with Q'. rewrite Q'_Divide_Property3;
  auto with Q'. rewrite (Q'_Mult_Commutation _ q); auto.
  assert (((g3 q)[n] + (Q'1 + Q'1)) ∈ Q'_N). 
  { apply Q'_N_Plus_in_Q'_N; auto. apply Q'_N_Plus_in_Q'_N; auto;
    apply Q'1_in_Q'_N; auto. }
  assert (((g3 q)[n] + Q'1) ∈ Q'_N).
  { apply Q'_N_Plus_in_Q'_N; auto. apply Q'1_in_Q'_N; auto. }
  assert (Q'0 < (Q'1 + Q'1)).
  { apply (Q'_Ord_Trans _ (Q'1 + Q'0)); auto with Q'.
    rewrite Q'_Plus_Property; auto with Q'.
    apply Q'_Plus_PrOrder; auto with Q'. }
  pose proof H16. pose proof H17. apply Q'_N_subset_Q' in H19,H20; auto.
  destruct (Q'_Ord_Tri (q · g2[n]) (((g3 q)[n] + (Q'1 + Q'1)) ·
  ((g3 q)[n] + (Q'1 + Q'1)))) as [H21|[|]]; auto with Q'.
  - assert (((g3 q)[n] + (Q'1 + Q'1)) ∈ (A n q)).
    { apply AxiomII; repeat split; eauto. }
    apply H13 in H22 as [].
    + assert ((g3 q)[n] + (Q'1 + Q'1) = (g3 q)[n] + Q'0).
      { rewrite Q'_Plus_Property; auto. }
      apply Q'_Plus_Cancellation in H23; auto with Q'. rewrite H23 in H18.
      elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'.
    + assert ((g3 q)[n] + (Q'1 + Q'1) < ((g3 q)[n] + Q'0)).
      { rewrite Q'_Plus_Property; auto. }
      apply Q'_Plus_PrOrder in H23; auto with Q'.
      apply (Q'_Ord_Trans Q'0) in H23; auto with Q'.
      elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'.
  - assert (((g3 q)[n] + Q'1) ∈ (A n q)).
    { apply AxiomII; repeat split; eauto. rewrite H21.
      apply Square_Root_Lemma4; auto.
      destruct (classic ((g3 q)[n] = Q'0)).
      - rewrite H22,Q'_Plus_Commutation,Q'_Plus_Property; auto with Q'.
      - assert ((g3 q)[n] ∈ (Q'_N ~ [Q'0])).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto.
          intro. apply MKT41 in H23; eauto with Q'. }
        apply Q'_N_Q'0_is_FirstMember in H23; auto.
        apply (Q'_Plus_PrOrder _ _ Q'1) in H23; auto with Q'.
        rewrite Q'_Plus_Property in H23; auto with Q'.
        right. apply (Q'_Ord_Trans _ Q'1); auto with Q'.
        rewrite Q'_Plus_Commutation; auto with Q'.
      - apply Q'_Plus_PrOrder; auto with Q'. pose proof Q'0_lt_Q'1.
        apply (Q'_Plus_PrOrder _ _ Q'1) in H22; auto with Q'.
        rewrite Q'_Plus_Property in H22; auto with Q'. }
    apply H13 in H22 as [].
    + assert ((g3 q)[n] + Q'1 = (g3 q)[n] + Q'0).
      { rewrite Q'_Plus_Property; auto. }
      apply Q'_Plus_Cancellation in H23; auto with Q'. elim Q'0_isnot_Q'1; auto.
    + assert (((g3 q)[n] + Q'1) < ((g3 q)[n] + Q'0)).
      { rewrite Q'_Plus_Property; auto. }
      apply Q'_Plus_PrOrder in H23; auto with Q'.
      apply (Q'_Ord_Trans Q'0) in H23; auto with Q'.
      elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'.
Qed.

(* 数列 g6/g2 有界 *)
Fact g6_g2_Fact2 : ∀ q, q ∈ Q'_Arch -> Q'0 < q
  -> ∃ qm, qm ∈ Q'_Arch /\ (∀ n, n ∈ ω -> (g6 q)[n]/ g2[n] < qm).
Proof.
  intros. pose proof H. apply (g6_Fact q) in H1 as [_]; auto.
  destruct g2_Fact1 as [_]; auto.
  assert (∀ n, n ∈ ω -> (g5 q)[n] ∈ Q'_N).
  { intros. destruct (g5_Fact q) as [[H4[]]_]; auto. rewrite <-H5 in H3.
    apply Property_Value,Property_ran in H3; auto. }
  assert (∀ n, n ∈ ω -> g1[n] ∈ Q'_N).
  { intros. destruct g1_Fact1 as [[H5[]]_]; auto. rewrite <-H6 in H4.
    apply Property_Value,Property_ran in H4; auto. }
  assert (∀ n, n ∈ ω -> Q'0 < g1[n]). { intros. apply g1_Fact2; auto. }
  assert (∀ n, n ∈ ω -> g1[n] <> Q'0).
  { intros. intro. pose proof (H5 n H6). rewrite H7 in H8.
    elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
  pose proof Q'_N_subset_Q'.
  assert (∀ n, n ∈ ω -> Q'0 = (g5 q)[n]/g1[n] \/ Q'0 < (g5 q)[n]/g1[n]).
  { intros. destruct (classic ((g5 q)[n] = Q'0)).
    - left. rewrite H9.
      apply (Q'_Mult_Cancellation g1[n]); auto with Q'.
      rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto with Q'.
    - assert ((g5 q)[n] ∈ (Q'_N ~ [Q'0])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. apply MKT41 in H10; eauto with Q'. }
      apply Q'_N_Q'0_is_FirstMember in H10; auto. right.
      apply (Q'_Mult_PrOrder _ _ g1[n]); auto with Q'.
      rewrite Q'_Mult_Property1,Q'_Divide_Property3; auto. }
  destruct (g5_g1_Fact q) as [q1[]]; auto. exists (q1 · q1).
  split. auto with Q'. intros. rewrite H1,H2,Q'_Frac_Square; auto.
  apply Square_Root_Lemma4; auto with Q'. apply Q'_Arch_subset_Q'; auto.
Qed.

Fact g4_g2_and_g6_g2 : ∀ q N, q ∈ Q'_Arch -> Q'0 < q -> N ∈ (N' ~ N'_N)
  -> (\[((Q'_extNatSeq (g4 q))[N] / (Q'_extNatSeq g2)[N])%q'\]
    = \[((Q'_extNatSeq (g6 q))[N] / (Q'_extNatSeq g2)[N])%q'\])%r. 
Proof.
  destruct NPAUF. intros. pose proof H3.
  apply MKT4' in H4 as [H4 _]. destruct g1_Fact1.
  assert (Q'_NatSeq φ4). { destruct φ4_is_Function as [[][]]. split; auto. }
  destruct g2_Fact1. pose proof H1. apply (g3_Fact q) in H10; auto.
  pose proof H1. apply (g4_Fact q) in H11 as []; auto.
  pose proof H1. apply (g5_Fact q) in H13 as []; auto.
  pose proof H1. apply (g6_Fact q) in H15 as []; auto.
  rewrite (Q'_extNatSeq_Property7 (g4 q) (g3 q)); auto.
  rewrite (Q'_extNatSeq_Property7 (g6 q) (g5 q)); auto.
  rewrite (Q'_extNatSeq_Property7 g2 g1); auto.
  assert ((Q'_extNatSeq g1)[N] ∈ Q' /\ (Q'_extNatSeq (g3 q))[N] ∈ Q'
    /\ (Q'_extNatSeq (g5 q))[N] ∈ Q') as [H17[]].
  { apply Q'_extNatSeq_is_Function in H5 as [H5[]]; auto.
    apply Q'_extNatSeq_is_Function in H10 as [H10[]]; auto.
    apply Q'_extNatSeq_is_Function in H13 as [H13[]]; auto.
    repeat split; apply Q'_N'_propersubset_Q'; auto;
    [apply H18|apply H20|apply H22];
    apply (@ Property_ran N),Property_Value; auto;
    [rewrite H17|rewrite H19|rewrite H21]; auto. }
  assert (∀ n, g1[n] <> Q'0).
  { intros. destruct (classic (n ∈ ω)).
    - apply (g1_Fact2 n) in H20; auto. intro. rewrite H21 in H20.
      elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'.
    - destruct H5 as [H5[]]. rewrite <-H21 in H20.
      apply MKT69a in H20. intro. pose proof H.
      elim MKT39. rewrite <-H20,H23; eauto with Q'. }
  assert ((Q'_extNatSeq g1)[N] <> Q'0).
  { apply Q'_extNatSeq_Property3; auto. apply Q'0_in_Q'_N; auto. }
  rewrite Q'_Frac_Square,Q'_Frac_Square; auto.
  assert (((Q'_extNatSeq (g3 q))[N] / (Q'_extNatSeq g1)[N]) ∈ Q'_Arch
    /\ ((Q'_extNatSeq (g5 q))[N] / (Q'_extNatSeq g1)[N]) ∈ Q'_Arch) as [].
  { pose proof H1. apply (g3_g1_Fact q) in H22 as [q1[]]; auto.
    pose proof H1. apply (g5_g1_Fact q) in H24 as [q2[]]; auto.
    split; [apply (Q'_extNatSeq_Property9 _ _ q1)|
    apply (Q'_extNatSeq_Property9 _ _ q2)]; auto. }
  pose proof Q'_N_subset_Q'.
  assert (\[ ((Q'_extNatSeq (g3 q))[N] / (Q'_extNatSeq g1)[N])%q' \]
    = \[ ((Q'_extNatSeq (g5 q))[N] / (Q'_extNatSeq g1)[N])%q' \])%r.
  { symmetry. apply R_Q'_Property; auto.
    assert ((Q'1 + Q'1) ∈ Q'_N).
    { apply Q'_N_Plus_in_Q'_N; auto; apply Q'1_in_Q'_N; auto. }
    rewrite (Q'_extNatSeq_Property6 (g5 q) (g3 q) (Q'1 + Q'1)),
    Q'_Divide_Distribution,Q'_Plus_Commutation,Q'_Mix_Association1,
    Q'_Minus_Property1,Q'_Plus_Property; auto with Q'.
    assert ((Q'1 / (Q'_extNatSeq g1)[N]) ∈ I).
    { pose proof Q'1_in_Q'_N.
      rewrite (Q'_extNatSeq_Property8 g1 Q'1 N); auto.
      destruct φ3_is_Function as [[][]]. pose proof φ3_ran.
      pose proof H4. rewrite <-H29 in H32.
      apply Property_Value,Property_ran in H32; auto.
      assert (Q'0 < (φ3[N] + Q'1)).
      { destruct (classic (φ3[N] = Q'0)).
        - rewrite Q'_Plus_Commutation,H33,Q'_Plus_Property; auto with Q'.
        - apply Q'_N'_Q'0_is_FirstMember in H33; auto.
          rewrite Q'_Plus_Commutation; auto.
          apply (Q'_Ord_Trans _ (Q'1 + Q'0)); auto with Q'.
          rewrite Q'_Plus_Property; auto with Q'.
          apply Q'_Plus_PrOrder; auto with Q'. rewrite <-H31; auto. }
      assert ((φ3[N] + Q'1) <> Q'0).
      { intro. rewrite H34 in H33.
        elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'. }
      assert ((φ3[N] + Q'1) · (Q'1 / (φ3[N] + Q'1)) = Q'1).
      { rewrite Q'_Divide_Property3; auto with Q'. }
      apply I_inv_Property2 in H35; auto with Q'.
      apply MKT4' in H35; tauto. apply MKT4'; split; auto with Q'.
      apply AxiomII; split. apply H30 in H32. eauto with Q'.
      intro. assert (φ3[N] ∈ Q'_Arch).
      { apply NNPP; intro.
        assert (φ3[N] ∈ (Q' ~ Q'_Arch)).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto. }
        apply (infinity_Plus_finity _ Q'1) in H38; auto.
        apply MKT4' in H38 as []. apply AxiomII in H39 as []; auto.
        apply Q'1_in_Q'_Arch; auto. }
      assert (|(φ3[N])| = φ3[N]).
      { destruct (classic (φ3[N] = Q'0)).
        - rewrite H38. apply eq_Q'0_Q'Abs; auto with Q'.
        - apply Q'_N'_Q'0_is_FirstMember in H38; auto.
          apply mt_Q'0_Q'Abs in H38; auto. rewrite <-H31; auto. }
      apply AxiomII in H37 as [_[_[k[]]]].
      assert (φ3⁻¹[k] ∈ N'_N).
      { rewrite <-Q'_N_PreimageSet_N'_N; auto.
        pose proof H37. apply Q'_N_propersubset_Q'_N' in H40; auto.
        rewrite <-H31,reqdi in H40.
        apply Property_Value,Property_ran in H40; auto. rewrite <-deqri in H40.
        apply AxiomII; repeat split; eauto. rewrite f11vi; auto.
        rewrite H31. apply Q'_N_propersubset_Q'_N'; auto. }
      pose proof H40. apply AxiomII in H41 as [_[a[]]].
      apply Fn_in_N'_N,(N'_Infty N) in H41; auto. rewrite <-H42 in H41.
      apply φ3_PrOrder in H41; auto; [ |apply N'_N_subset_N']; auto.
      rewrite f11vi in H41; auto;
      [ |rewrite H31; apply Q'_N_propersubset_Q'_N']; auto. rewrite H38 in H39.
      destruct H39; [rewrite H39 in H41|apply (Q'_Ord_Trans k) in H39]; auto;
      elim (Q'_Ord_irReflex k k); auto. }
    rewrite Q'_Divide_Distribution; auto with Q'. }
  rewrite <-R_Mult_Instantiate,<-R_Mult_Instantiate,H25; auto.
Qed.

End square_root_arguments.

Import square_root_arguments.

Lemma Square_Root_Lemma8 : ∀ r, r ∈ Ｒ -> (R0 < r)%r
  -> ∃ r1, r1 ∈ Ｒ /\ (r = r1 · r1)%r.
Proof.
  destruct NPAUF. intros. pose proof H1. inR H3 q.
  assert (Q'0 < q).
  { rewrite H5 in H2. apply R_Ord_Instantiate in H2 as []; auto.
    apply Q'0_in_Q'_Arch; auto. }
  assert ((N' ~ N'_N) <> Φ).
  { intro. destruct N'_N_propersubset_N' as [_]; auto. elim H8.
    apply AxiomI; split; intros. apply N'_N_subset_N'; auto.
    apply NNPP; intro. elim (@ MKT16 z); auto. rewrite <-H7.
    apply MKT4'; split; auto. apply AxiomII; split; eauto. }
  apply NEexE in H7 as [N]. pose proof H.
  assert (∀ m, m ∈ ω -> ((g4 q)[m] / g2[m]) < q).
  { intros. apply g4_g2_Fact; auto. }
  assert (∀ m, m ∈ ω -> q < ((g6 q)[m] / g2[m])).
  { intros. apply g6_g2_Fact1; auto. }
  pose proof H3. apply (g6_g2_Fact2 q) in H11 as [q1[]]; auto.
  pose proof H7. apply MKT4' in H13 as [H13 _].
  destruct g2_Fact1 as [H14 _].
  pose proof H3. apply (g4_Fact q) in H15 as [H15 _]; auto.
  pose proof H3. apply (g6_Fact q) in H16 as [H16 _]; auto.
  assert (∀ m, m ∈ ω -> Q'0 < g2[m]). { intros. apply g2_Fact2; auto. }
  assert (∀ m, g2[m] <> Q'0).
  { intros. destruct (classic (m ∈ ω)). intro. pose proof (H17 m H18).
    rewrite H19 in H20. elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'.
    intro. destruct H14 as [H14[]]. rewrite <-H20 in H18. apply MKT69a in H18.
    elim MKT39. rewrite <-H18,H19; eauto with Q'. }
  apply (Q'_extNatSeq_Property10 _ _ q N) in H9; auto.
  apply (Q'_extNatSeq_Property12 _ _ q q1 N) in H10; auto.
  rewrite g4_g2_and_g6_g2 in H9; auto.
  assert ((\[ ((Q'_extNatSeq (g6 q))[N] / (Q'_extNatSeq g2)[N])%q' \]) ∈ Ｒ)%r.
  { apply R_Instantiate2; auto. apply (Q'_extNatSeq_Property9 _ _ q1); auto. }
  assert (\[q\] = \[ ((Q'_extNatSeq (g6 q))[N] / (Q'_extNatSeq g2)[N])%q' \])%r.
  { apply Square_Root_Lemma6; auto. rewrite <-H5; auto. }
  pose proof H3. apply (g6_Fact q) in H21 as [_]; auto.
  destruct g2_Fact1 as [_]; auto. destruct g1_Fact1 as [H23 _]; auto.
  pose proof H3. apply (g5_Fact q) in H24 as [H24 _]; auto.
  rewrite (Q'_extNatSeq_Property7 (g6 q) (g5 q) N) in H20; auto.
  rewrite (Q'_extNatSeq_Property7 g2 g1 N) in H20; auto.
  assert ((Q'_extNatSeq (g5 q))[N] ∈ Q' /\ (Q'_extNatSeq g1)[N] ∈ Q') as [].
  { apply Q'_extNatSeq_is_Function in H23 as [H23[]]; auto.
    apply Q'_extNatSeq_is_Function in H24 as [H24[]]; auto.
    split; apply Q'_N'_propersubset_Q'; auto; [apply H28|apply H26];
    apply (@ Property_ran N),Property_Value; auto;
    [rewrite H27|rewrite H25]; auto. }
  assert (∀ n, g1[n] <> Q'0).
  { intros. destruct H23 as [H23[]]. destruct (classic (n ∈ ω)).
    - apply (g1_Fact2) in H29; auto. intro. rewrite H30 in H29.
      elim (Q'_Ord_irReflex Q'0 Q'0); auto with Q'.
    - rewrite <-H27 in H29. apply MKT69a in H29. intro.
      elim MKT39. rewrite <-H29,H30; eauto with Q'. }
  assert ((Q'_extNatSeq g1)[N] <> Q'0).
  { apply Q'_extNatSeq_Property3; auto. apply Q'0_in_Q'_N; auto. }
  rewrite Q'_Frac_Square in H20; auto.
  exists (\[ ((Q'_extNatSeq (g5 q))[N] / (Q'_extNatSeq g1)[N])%q' \])%r.
  assert (((Q'_extNatSeq (g5 q))[N] / (Q'_extNatSeq g1)[N]) ∈ Q'_Arch).
  { pose proof H3. apply (g5_g1_Fact q) in H29 as [q2[]]; auto.
    apply (Q'_extNatSeq_Property9 _ _ q2); auto. }
  split. apply R_Instantiate2; auto. rewrite R_Mult_Instantiate,H5; auto.
Qed.

Open Scope r_scope.

Lemma Square_Root_Lemma9 : ∀ r, r ∈ Ｒ -> R0 < r
  -> ∃ r1, r1 ∈ Ｒ /\ R0 < r1 /\ r = r1 · r1.
Proof.
  destruct NPAUF. intros. pose proof H2.
  apply Square_Root_Lemma8 in H3 as [r1[]]; auto.
  destruct (R_Ord_Tri R0 r1) as [H5|[|]]; auto with R. eauto.
  - apply R_Plus_PrOrder_Corollary in H5 as [r1'[[H5[]]_]]; auto with R.
    exists r1'. repeat split; auto. apply R_Minus_Plus in H7; auto with R.
    rewrite <-H7,R_Mult_Distribution_Minus,R_Mult_Commutation,
    R_Mult_Distribution_Minus,R_Mult_Property1,R_Mult_Commutation,
    R_Mult_Property1,R_Minus_Property2,R_Mult_Commutation,
    R_Mult_Distribution_Minus,R_Mult_Property1,<-H4; auto with R.
    symmetry. apply R_Minus_Plus; auto with R.
    rewrite R_Plus_Commutation,<-R_Mix_Association1,
    R_Plus_Property,R_Minus_Property1; auto with R.
  - rewrite H4,<-H5,R_Mult_Property1,H5 in H2; auto with R.
    elim (R_Ord_irReflex r1 r1); auto.
Qed.

Lemma Square_Root_Lemma10 : ∀ r, r ∈ Ｒ -> R0 < r
  -> ∃! r1, r1 ∈ Ｒ /\ R0 < r1 /\ r = r1 · r1.
Proof.
  destruct NPAUF. intros. pose proof H2.
  apply Square_Root_Lemma9 in H3 as [r1[H3[]]]; auto.
  exists r1. split; auto. intros r2 [H6[]].
  assert (r1 <> R0 /\ r2 <> R0) as [].
  { split; intro; [rewrite H9 in H4|rewrite H9 in H7];
    elim (R_Ord_irReflex R0 R0); auto with R. }
  destruct (R_Ord_Tri r1 r2) as [H11|[|]]; auto.
  - pose proof H11. apply (R_Mult_PrOrder _ _ r1) in H11; auto.
    apply (R_Mult_PrOrder _ _ r2) in H12; auto.
    rewrite <-H5,R_Mult_Commutation in H11; auto.
    rewrite <-H8 in H12. apply (R_Ord_Trans r) in H12; auto with R.
    elim (R_Ord_irReflex r r); auto.
  - pose proof H11. apply (R_Mult_PrOrder _ _ r1) in H11; auto.
    apply (R_Mult_PrOrder _ _ r2) in H12; auto.
    rewrite <-H5,R_Mult_Commutation in H11; auto.
    rewrite <-H8 in H12. apply (R_Ord_Trans r) in H11; auto with R.
    elim (R_Ord_irReflex r r); auto.
Qed.

Definition Square_Root r := ∩(\{ λ u, u ∈ Ｒ /\ R0 < u /\  u · u = r \}).

Notation "√ r" := (Square_Root r)(at level 5) : r_scope.

Property Square_Root_Property : ∀ r, r ∈ Ｒ -> R0 < r
  -> √r ∈ Ｒ /\ R0 < √r /\ √r · √r = r.
Proof.
  intros. pose proof H. apply Square_Root_Lemma10 in H1 as [r1[[H1[]]]]; auto.
  assert (\{ λ u, u ∈ Ｒ /\ R0 < u /\  u · u = r \} = [r1]).
  { apply AxiomI; split; intros. apply AxiomII in H5 as [H5[H6[]]].
    apply MKT41; eauto. symmetry. apply H4; auto. apply MKT41 in H5; eauto.
    rewrite H5. apply AxiomII; split; eauto. }
  assert (Ensemble r1); eauto. apply MKT44 in H6 as [].
  unfold Square_Root. rewrite H5,H6; auto.
Qed.

Definition R2 := R1 + R1.

Property R2_Property : R2 ∈ Ｎ /\ R0 < R2.
Proof.
  intros. split. unfold R2. auto with R.
  apply (R_Ord_Trans _ R1); auto with R; [unfold R2; auto with R| ].
  replace R1 with (R1 + R0). apply R_Plus_PrOrder; auto with R.
  rewrite R_Plus_Property; auto with R.
Qed.

Definition φω := φn ∘ φ4.

Property φω_is_Function : Function1_1 φω /\ dom(φω) = ω /\ ran(φω) = Ｎ.
Proof.
  intros. destruct φ4_is_Function as [[][]].
  destruct φn_is_Function as [[][]]. unfold Q'_N in H5. split. split.
  apply MKT64; auto. unfold φω. rewrite MKT62. apply MKT64; auto.
  split; apply AxiomI; split; intros.
  - apply AxiomII in H7 as [_[]]. apply AxiomII' in H7 as [_[x0[]]].
    apply Property_dom in H7. rewrite H1 in H7; auto.
  - apply AxiomII; split; eauto. rewrite <-H1 in H7.
    apply Property_Value in H7; auto. pose proof H7.
    apply Property_ran in H8. rewrite <-H5 in H8.
    apply Property_Value in H8; auto. exists φn[φ4[z]].
    apply AxiomII'; split; eauto. apply Property_dom in H7.
    apply Property_ran in H8. apply MKT49a; eauto.
  - apply AxiomII in H7 as [_[]]. apply AxiomII' in H7 as [_[x0[]]].
    apply Property_ran in H8. rewrite H6 in H8; auto.
  - apply AxiomII; split; eauto. rewrite <-H6 in H7.
    apply AxiomII in H7 as [_[]]; auto. pose proof H7.
    apply Property_dom in H8. rewrite H5 in H8.
    apply AxiomII in H8 as [_[]]. exists x0.
    apply AxiomII'; split; eauto. apply Property_ran in H7.
    apply Property_dom in H8. apply MKT49a; eauto.
Qed.

Lemma φω_Lemma : ∀ m, m ∈ ω -> φn[φ4[m]] = φω[m].
Proof.
  intros. destruct φ4_is_Function as [[][]].
  destruct φn_is_Function as [[][]]. unfold Q'_N in H6. pose proof H.
  rewrite <-H2 in H8. apply Property_Value in H8; auto. pose proof H8.
  apply Property_ran in H9. rewrite <-H6 in H9. apply Property_Value in H9;
  auto. assert ([m,φn[φ4[m]]] ∈ φω).
  { apply AxiomII'; split; eauto. apply Property_ran in H9.
    apply MKT49a; eauto. }
  destruct φω_is_Function as [[][]]. pose proof H. rewrite <-H13 in H15.
  apply Property_Value in H15; auto. destruct H11. apply (H16 m); auto.
Qed.

(* φω保序 *)
Property φω_PrOrder : ∀ u v, u ∈ ω -> v ∈ ω -> u ∈ v <-> φω[u] < φω[v].
Proof.
  intros. destruct φ4_is_Function as [[][]].
  destruct φn_is_Function as [[][]].
  pose proof H. rewrite <-H3 in H9.
  apply Property_Value,Property_ran in H9; auto.
  pose proof H0. rewrite <-H3 in H10.
  apply Property_Value,Property_ran in H10; auto.
  split; intros. rewrite <-φω_Lemma,<-φω_Lemma; auto.
  apply φn_PrOrder; auto. apply ->φ4_PrOrder; auto.
  rewrite <-φω_Lemma,<-φω_Lemma in H11; auto.
  apply φn_PrOrder,φ4_PrOrder in H11; auto.
Qed.

(* φω加法保持 *)
Property φω_PrPlus : ∀ u v, u ∈ ω -> v ∈ ω -> φω[(u + v)%ω] = φω[u] + φω[v].
Proof.
  intros. destruct φ4_is_Function as [[][]].
  destruct φn_is_Function as [[][]].
  rewrite <-φω_Lemma; auto; [ |apply ω_Plus_in_ω; auto].
  rewrite φ4_PrPlus; auto. pose proof H. pose proof H0.
  rewrite <-H3 in H9,H10. apply Property_Value,Property_ran in H9,H10; auto.
  rewrite φn_PrPlus,φω_Lemma,φω_Lemma; auto.
Qed.

(* φω乘法保持 *)
Property φω_PrMult : ∀ u v, u ∈ ω -> v ∈ ω -> φω[(u · v)%ω] = φω[u] · φω[v].
Proof.
  intros. destruct φ4_is_Function as [[][]].
  destruct φn_is_Function as [[][]].
  rewrite <-φω_Lemma; auto; [ |apply ω_Mult_in_ω; auto].
  rewrite φ4_PrMult; auto. pose proof H. pose proof H0.
  rewrite <-H3 in H9,H10. apply Property_Value,Property_ran in H9,H10; auto.
  rewrite φn_PrMult,φω_Lemma,φω_Lemma; auto.
Qed.

Property φω_0 : φω[0] = R0.
Proof. intros. rewrite <-φω_Lemma,φ4_0,φn_Q'0; auto. Qed.

Property φω_1 : φω[1] = R1.
Proof. intros. rewrite <-φω_Lemma,φ4_1,φn_Q'1; auto. apply in_ω_1. Qed.

Property φω_2 : φω[2] = R2.
Proof.
  intros. rewrite <-φω_Lemma; auto; [ |apply in_ω_2].
  replace 2 with (1 + 1)%ω. rewrite φ4_PrPlus,φ4_1,φn_PrPlus,φn_Q'1;
  try apply Q'1_in_Q'_N; auto; apply in_ω_1.
  assert (1 + (PlusOne 0) = 2)%ω.
  { rewrite Plus_Property2_a,Plus_Property1_a; auto; apply in_ω_1. }
  replace (PlusOne 0) with 1 in H; auto. unfold PlusOne. rewrite MKT17; auto.
Qed.

Definition R_Even r := ∃ n, n ∈ Ｚ /\ r = R2 · n.

Definition R_Odd r := ∃ n, n ∈ Ｚ /\ r = (R2 · n) + R1.

Property R_Even_in_Z : ∀ r, R_Even r -> r ∈ Ｚ.
Proof.
  intros. destruct H as [n[]]. rewrite H0. apply Z_Mult_in_Z; auto.
  apply N_propersubset_Z,R2_Property; auto.
Qed.

Property R_Odd_in_Z : ∀ r, R_Odd r -> r ∈ Ｚ.
Proof.
  intros. destruct H as [n[]]. rewrite H0. apply Z_Plus_in_Z; auto.
  apply R_Even_in_Z; auto. unfold R_Even; eauto. apply R1_in_Z; auto.
Qed.

Property R_Even_Odd_Property1 : ∀ r, r ∈ Ｚ -> R_Even r \/ R_Odd r.
Proof.
  intros. destruct φω_is_Function as [[][]]. set (r1 := |r|).
  assert (r1 ∈ Ｎ).
  { rewrite N_equ_Z_me_R0; auto. pose proof H.
    apply Z_propersubset_R,RAbs_in_R in H4; auto.
    pose proof H. apply Z_propersubset_R in H5; auto.
    apply AxiomII; repeat split; eauto.
    pose proof H5. apply (R_Ord_Tri r R0) in H6 as [H6|[|]]; auto with R.
    apply lt_R0_RAbs in H6; auto. unfold r1. rewrite H6.
    apply Z_Minus_in_Z; auto with R. apply mt_R0_RAbs in H6; auto. unfold r1.
    rewrite H6; auto. apply eq_R0_RAbs in H6; auto. unfold r1.
    rewrite H6; auto with R. apply R0_le_RAbs in H5 as [_[]]; auto. }
  assert (R_Even r1 \/ R_Odd r1).
  { rewrite <-H3 in H4. apply Einr in H4 as [x[]]; auto.
    rewrite H2 in H4. destruct (classic (x ∈ ω_E)).
    apply AxiomII in H6 as [_[n[]]].
    rewrite H7,φω_PrMult,φω_2 in H5; auto; [ |apply in_ω_2]. left. exists φω[n].
    rewrite <-H2 in H6. apply Property_Value,Property_ran in H6; auto.
    rewrite H3 in H6. apply N_propersubset_Z in H6; auto.
    assert (x ∈ ω_O).
    { rewrite <-ω_E_Union_ω_O in H4. apply MKT4 in H4 as []; auto.
      elim H6; auto. }
    apply AxiomII in H7 as [_[n[]]].
    rewrite H8,φω_PrPlus,φω_1,φω_PrMult,φω_2 in H5; try apply ω_Mult_in_ω; auto;
    try apply in_ω_2; try apply in_ω_1. right. exists φω[n]. rewrite <-H2 in H7.
    apply Property_Value,Property_ran in H7; auto. rewrite H3 in H7.
    apply N_propersubset_Z in H7; auto. }
  pose proof H. apply Z_propersubset_R in H6; auto.
  pose proof H6. apply (R_Ord_Tri R0) in H7 as [H7|[|]]; auto with R.
  apply mt_R0_RAbs in H7; auto. rewrite <-H7; auto. apply lt_R0_RAbs in H7; auto.
  destruct H5 as [[m[]]|[m[]]]. left. exists (R0 - m). split.
  apply Z_Minus_in_Z; auto with R. unfold r1.
  rewrite R_Mult_Distribution_Minus,R_Mult_Property1; auto with R;
  try apply N_propersubset_R,R2_Property; auto;
  try apply Z_propersubset_R; auto. rewrite <-H8. unfold r1. rewrite H7.
  symmetry. apply R_Minus_Plus; auto with R.
  rewrite R_Plus_Commutation; auto with R. apply R_Minus_Plus; auto with R.
  right. exists (R0 - (m + R1)). split. auto with R. pose proof H5.
  apply Z_propersubset_R in H9; auto.
  rewrite R_Mult_Distribution_Minus,R_Mult_Property1,
  R_Mult_Distribution,R_Mult_Property2; auto with R;
  try apply N_propersubset_R,R2_Property; auto.
  assert (R2 ∈ Ｒ). { apply N_propersubset_R,R2_Property; auto. }
  rewrite R_Plus_Commutation,<-R_Mix_Association1,R_Plus_Property; auto with R.
  symmetry in H8. assert (r1 ∈ Ｒ). { apply N_propersubset_R; auto. }
  replace ((R2 · m) + R2) with (((R2 · m) + R1) + R1).
  rewrite H8. unfold r1. rewrite H7. symmetry. apply R_Minus_Plus; auto with R.
  rewrite R_Plus_Association,(R_Plus_Commutation _ r),<-(R_Plus_Association),
  (R_Plus_Commutation _ r),<-R_Mix_Association1,R_Plus_Property,
  R_Minus_Property1,R_Plus_Commutation,R_Plus_Property; auto with R.
  rewrite R_Plus_Association; auto with R. rewrite <-H7. left. exists R0.
  rewrite R_Mult_Property1; auto with R.
  apply N_propersubset_R,R2_Property; auto.
Qed.

Property R_Even_Odd_Property2 : ∀ r, r ∈ Ｚ -> ~ (R_Even r /\ R_Odd r).
Proof.
  intros. intro. destruct H0 as [[m[]][n[]]].
  rewrite H1 in H3. destruct R2_Property.
  assert (R2 ∈ Ｒ /\ R2 <> R0) as [].
  { split. apply N_propersubset_R; auto. intro. rewrite H6 in H5.
    elim (R_Ord_irReflex R0 R0); auto. }
  pose proof H0. pose proof H2. apply Z_propersubset_R in H8,H9; auto.
  assert (m = n + (R1 / R2)).
  { apply (R_Mult_Cancellation R2); auto with R.
    rewrite R_Mult_Distribution,R_Divide_Property3; auto with R. }
  symmetry in H10. apply R_Minus_Plus in H10; auto with R.
  assert ((R1 / R2) ∈ Ｚ). { rewrite <-H10. apply Z_Minus_in_Z; auto. }
  assert (R0 < (R1 / R2)).
  { apply (R_Mult_PrOrder _ _ R2); auto with R.
    rewrite R_Mult_Property1,R_Divide_Property3; auto with R. }
  assert ((R1 / R2) < R1).
  { apply (R_Mult_PrOrder _ _ R2); auto with R.
    rewrite R_Mult_Property2,R_Divide_Property3; auto with R.
    replace R1 with (R1 + R0). apply R_Plus_PrOrder; auto with R.
    rewrite R_Plus_Property; auto with R. }
  assert (R1 < (R1 / R2) \/ R1 = (R1 / R2)).
  { pose proof H11. apply AxiomII in H14 as [_[z[]]].
    rewrite H15 in H12. apply R_Ord_Instantiate in H12 as []; auto;
    try apply Q'_Z_propersubset_Q'_Arch; try apply Q'0_in_Q'_Z; auto.
    apply Square_Root_Lemma1 in H12; auto; [ |apply Q'0_in_Q'_Z; auto].
    rewrite Q'_Plus_Commutation,Q'_Plus_Property in H12; auto with Q'.
    destruct H12. apply Q'_Ord_to_R_Ord in H12; auto;
    try apply Q'_Z_propersubset_Q'_Arch; try apply Q'1_in_Q'_Z; auto.
    rewrite H15; destruct H12; auto. right. rewrite H15,<-H12; auto. }
  destruct H14; [apply (R_Ord_Trans R1) in H13|rewrite <-H14 in H13];
  auto with R; elim (R_Ord_irReflex R1 R1); auto.
Qed.

Property R_Even_Odd_Property3 : ∀ r1 r2, R_Even r1 -> R_Even r2
  -> R_Even (r1 · r2).
Proof.
  intros. destruct H as [m[]]. exists (m · r2).
  apply R_Even_in_Z in H0; auto. split. auto with R.
  rewrite <-R_Mult_Association; auto; try (apply N_propersubset_R,R2_Property);
  try apply Z_propersubset_R; auto. rewrite <-H1; auto.
Qed.

Property R_Even_Odd_Property4 : ∀ r1 r2, R_Odd r1 -> R_Odd r2 -> R_Odd (r1 · r2).
Proof.
  intros. destruct H as [m[]]. destruct H0 as [n[]].
  assert (m ∈ Ｒ /\ n ∈ Ｒ) as []. { split; apply Z_propersubset_R; auto. }
  assert (R2 ∈ Ｒ). { apply N_propersubset_R,R2_Property; auto. }
  rewrite H1,H2,R_Mult_Distribution,(R_Mult_Commutation _ (R2 · n)),
  R_Mult_Distribution,R_Mult_Property2,R_Mult_Association,<-R_Mult_Distribution,
  (R_Mult_Commutation _ R1),(R_Mult_Distribution R1),R_Mult_Property2,
  (R_Mult_Commutation R1),R_Mult_Property2,<-R_Plus_Association,
  <-R_Mult_Distribution; auto with R.
  assert (R2 ∈ Ｚ). { apply N_propersubset_Z,R2_Property; auto. }
  exists (((n · (R2 · m)) + n) + m); split; auto with R.
Qed.

(* 对于Q中任意正数, 总有唯一的最小分母的分数表示.
   即任意q, 总有唯一的N中的m, q = (q*m)/m 并且m小于所有使得 q=a/u 的u   *)
Lemma Existence_of_irRational_Numbers_Lemma : ∀ q, q ∈ Ｑ -> R0 < q
  -> ∃ m, (m · q) ∈ Ｎ /\ FirstMember m R_Ord
    (\{ λ u, u ∈ Ｎ /\ u <> R0 /\ ∃ a, a ∈ Ｎ /\ q = a/u \}).
Proof.
  intros. pose proof H. apply AxiomII in H1 as [_[q1[]]].
  pose proof H0. rewrite H2 in H3. apply R_Ord_Instantiate in H3 as [];
  try apply Q'_Q_subset_Q'_Arch; try apply Q'0_in_Q'_Q; auto. pose proof H1.
  apply RatSeq_and_NatSeq_Lemma in H5 as [m1[[H5[]]_]]; auto.
  apply AxiomII in H6 as [_[H6[H8[n1[]]]]]. exists (\[m1\]). split.
  rewrite H2,R_Mult_Instantiate,H10,Q'_Divide_Property3; auto;
  try apply Q'_N_subset_Q'; auto;
  [ |apply Q'_N_propersubset_Q'_Arch|apply Q'_Q_subset_Q'_Arch]; auto.
  apply AxiomII; split; eauto.
  assert ((\[n1\]) ∈ Ｒ).
  { apply R_Instantiate2. apply Q'_N_propersubset_Q'_Arch; auto. }
  eauto. assert ((\[m1\]) ∈ Ｒ).
  { apply R_Instantiate2. apply Q'_N_propersubset_Q'_Arch; auto. }
  assert ((\[m1\]) <> R0).
  { assert (R0 <> R1).
    { intro. pose proof R0_lt_R1. rewrite H12 in H13.
      elim (R_Ord_irReflex R1 R1); auto with R. }
    assert (m1 ∈ (Q'_N ~ [Q'0])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
      apply MKT41 in H13; eauto with Q'. }
    apply Q'_N_Q'0_is_FirstMember,Square_Root_Lemma1 in H13; auto;
    try apply Q'_N_propersubset_Q'_Z; try apply Q'0_in_Q'_N; auto.
    rewrite Q'_Plus_Commutation,Q'_Plus_Property in H13; auto with Q'.
    assert (R0 <> R1).
    { intro. pose proof R0_lt_R1. rewrite H14 in H15.
      elim (R_Ord_irReflex R1 R1); auto with R. }
    destruct H13. apply Q'_Ord_to_R_Ord in H13;
    try apply Q'_N_propersubset_Q'_Arch; try apply Q'1_in_Q'_N; auto.
    destruct H13. rewrite <-H13; auto. intro. rewrite H15 in H13.
    replace (\[Q'1\]) with R1 in H13; auto.
    apply (R_Ord_Trans R0) in H13; auto with R.
    elim (R_Ord_irReflex R0 R0); auto with R. rewrite <-H13; auto. }
  split. apply AxiomII; repeat split; eauto. apply AxiomII; split; eauto.
  exists (\[(m1 · q1)%q'\]). assert ((\[(m1 · q1)%q'\]) ∈ Ｒ).
  { apply R_Instantiate2; try apply Q'_N_propersubset_Q'_Arch; auto. }
  split. apply AxiomII; split; eauto. symmetry. apply R_Divide_Mult; auto.
  apply Q_subset_R; auto. rewrite H2,R_Mult_Instantiate; auto.
  apply Q'_N_propersubset_Q'_Arch; auto. apply Q'_Q_subset_Q'_Arch; auto.
  intros. apply AxiomII in H13 as [_[H13[H14[x[]]]]]. pose proof H13.
  apply AxiomII in H17 as [_[y1[]]]. intro. apply (H7 y1).
  apply AxiomII; repeat split; eauto. intro. rewrite H20 in H18; auto.
  pose proof H15. apply AxiomII in H20 as [_[x1[]]]. exists x1. split; auto.
  assert (q = \[(x1 / y1)%q'\]).
  { symmetry in H16. apply R_Divide_Mult in H16; try apply Q_subset_R; auto;
    try apply Z_propersubset_Q,N_propersubset_Z; auto.
    rewrite H18,H2,H21,R_Mult_Instantiate in H16; auto;
    [ |apply Q'_N_propersubset_Q'_Arch|apply Q'_Q_subset_Q'_Arch]; auto.
    apply (R_Mult_Cancellation y); auto. apply N_propersubset_R; auto.
    apply Q_subset_R; auto. apply R_Instantiate2; auto.
    apply Q'_Q_subset_Q'_Arch; auto. apply Q'_Z_Divide_in_Q'_Q; auto;
    try apply Q'_N_propersubset_Q'_Z; auto. intro. rewrite H22 in H18; auto.
    rewrite H2,H18,R_Mult_Instantiate,R_Mult_Instantiate; auto.
    rewrite Q'_Divide_Property3; auto; try apply Q'_N_subset_Q'; auto.
    intro. rewrite H22 in H18; auto. apply Q'_N_propersubset_Q'_Arch; auto.
    apply Q'_Q_subset_Q'_Arch,Q'_Z_Divide_in_Q'_Q; auto;
    try apply Q'_N_propersubset_Q'_Z; auto. intro. rewrite H22 in H18; auto.
    apply Q'_N_propersubset_Q'_Arch; auto. apply Q'_Q_subset_Q'_Arch; auto. }
  pose proof H. apply Q'_RatSeq_and_R_RatSeq_Lemma in H23 as [q0[[]]]; auto.
  replace q1 with q0. apply H25. split; auto. apply Q'_Z_Divide_in_Q'_Q; auto;
  try apply Q'_N_propersubset_Q'_Z; auto. intro. rewrite H26 in H18; auto.
  apply H25; auto. rewrite H18 in H19. apply R_Ord_Instantiate in H19 as [];
  auto; apply Q'_N_propersubset_Q'_Arch; auto.
Qed.

Property Existence_of_irRational_Numbers : √R2 ∈ (Ｒ ~ Ｑ).
Proof.
  destruct NPAUF. intros. destruct R2_Property. pose proof H1.
  apply N_propersubset_R in H3; auto. pose proof H3.
  apply Square_Root_Property in H4 as [H4[]]; auto.
  apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
  apply Existence_of_irRational_Numbers_Lemma in H7 as [x[]]; auto.
  destruct H8. apply AxiomII in H8 as [_[H8[H10[y[]]]]].
  pose proof H8. pose proof H11. apply N_propersubset_R in H13,H14; auto.
  symmetry in H12. apply R_Divide_Mult in H12; auto.
  pose proof H8. pose proof H11. apply N_propersubset_Z in H15,H16; auto.
  assert (R2 · (x · x) = (y · y)).
  { rewrite <-H6,R_Mult_Association,<-(R_Mult_Association _ x x),
    (R_Mult_Commutation (√R2) x),H12,R_Mult_Commutation,R_Mult_Association,H12;
    auto with R. }
  assert (R_Even (y · y)). { exists (x · x). split; auto with R. }
  assert (R_Even y).
  { pose proof H16. apply R_Even_Odd_Property1 in H19 as []; auto.
    elim (R_Even_Odd_Property2 (y · y)); auto with R.
    split; auto. apply R_Even_Odd_Property4; auto. }
  destruct H19 as [m[]]. pose proof H19. apply Z_propersubset_R in H21; auto.
  rewrite H20,R_Mult_Association in H17; auto with R.
  assert (R2 <> R0).
  { intro. rewrite H22 in H2. elim (R_Ord_irReflex R0 R0); auto. }
  apply R_Mult_Cancellation in H17; auto with R.
  rewrite (R_Mult_Commutation m),R_Mult_Association in H17; auto with R.
  assert (R_Even (x · x)). { exists (m · m). split; auto with R. }
  assert (R_Even x).
  { pose proof H15. apply R_Even_Odd_Property1 in H24 as []; auto.
    elim (R_Even_Odd_Property2 (x · x)); auto with R.
    split; auto. apply R_Even_Odd_Property4; auto. }
  destruct H24 as [n[]]. assert (n <> R0).
  { intro. rewrite H26,R_Mult_Property1 in H25; auto. }
  assert (√R2 = m / n).
  { apply R_Divide_Mult in H12; auto. rewrite <-H12,H20,H25.
    apply Z_propersubset_R in H19,H24; auto. apply R_Divide_Mult; auto with R.
    intro. apply R_Mult_Property3 in H27 as []; auto.
    rewrite R_Mult_Association; auto with R. rewrite R_Divide_Property3; auto. }
  assert (n ∈ Ｎ).
  { rewrite N_equ_Z_me_R0; auto. apply AxiomII; repeat split; eauto.
    assert (R0 < x). { apply N_R0_is_FirstMember; auto. }
    replace R0 with (R2 · R0) in H28.
    rewrite H25 in H28. apply R_Mult_PrOrder in H28; auto with R.
    apply Z_propersubset_R; auto. rewrite R_Mult_Property1; auto. }
  assert (m ∈ Ｎ).
  { rewrite N_equ_Z_me_R0; auto. apply AxiomII; repeat split; eauto.
    destruct (classic (y = R0)). left. rewrite H20 in H29.
    apply R_Mult_Property3 in H29 as []; auto. rewrite H29 in H2.
    elim (R_Ord_irReflex R0 R0); auto.
    assert (R0 < y). { apply N_R0_is_FirstMember; auto. }
    replace R0 with (R2 · R0) in H30.
    rewrite H20 in H30. apply R_Mult_PrOrder in H30; auto with R.
    rewrite R_Mult_Property1; auto. }
  assert (n < x).
  { pose proof H24. apply Z_propersubset_R in H30; auto.
    replace n with (n + R0). rewrite H25,R_Mult_Commutation; auto. unfold R2.
    rewrite R_Mult_Distribution,R_Mult_Property2; auto with R.
    apply R_Plus_PrOrder; auto with R. apply N_R0_is_FirstMember; auto.
    rewrite R_Plus_Property; auto. }
  apply (H9 n); auto. apply AxiomII; repeat split; eauto.
Qed.

Property Q_propersubset_R : Ｑ ⊂ Ｒ /\ Ｑ <> Ｒ.
Proof.
  split. apply Q_subset_R. intro. pose proof Existence_of_irRational_Numbers.
  apply MKT4' in H0 as []. rewrite <-H in H0. apply AxiomII in H1 as []; auto.
Qed.

































