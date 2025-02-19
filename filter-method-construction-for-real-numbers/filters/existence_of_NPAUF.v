(*       This file presents the formal verification of the           *)
(*   existence of non-principal arithmetical ultrafilters (NPAUF)    *)
(*             using the Continumm Hypothesis (CH).                  *)
(*  It is developmented in the CoqIDE (version 8.13.2) for windows.  *)

(** existence_of_NPAUF *)

Require Export filters.arithmetical_ultrafilter.
Require Export filters.filter_extension.

Notation Fσ := (filter.Fσ ω).
Notation F := (filter.F ω).
Notation βω := (arithmetical_ultrafilter.β ω).
Notation Const n := (arithmetical_ultrafilter.Const ω n).
Notation "f 〈 F0 〉" := (f〈F0∣ω〉)(at level 5).
Notation "f =_ F0 g" := (arithmetical_ultrafilter.AlmostEqual f g ω ω F0)
  (at level 10, F0 at level 9).
Notation "〈 G 〉→ᶠ" := (〈G∣ω〉→ᶠ).

Lemma Existence_of_NPAUF_Lemma1 :
  ∀ F0 f g, F0 ∈ β ω -> Function f -> Function g
  -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
  -> (∃ n, n ∈ ω /\ (f〈F0〉 = F n \/ g〈F0〉 = F n))
  -> f〈F0〉 = g〈F0〉 -> f =_F0 g.
Proof.
  assert (∀ F0 f g, F0 ∈ βω -> Function f -> Function g
    -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
    -> (∃ n, n ∈ ω /\ g〈F0〉 = F n) -> f〈F0〉 = g〈F0〉 -> f =_F0 g).
  { intros. destruct H6 as [n[]]. rewrite H8 in H7.
    assert ([n] ∈ f〈 F0 〉).
    { rewrite H7. apply AxiomII; repeat split; eauto.
      unfold Included; intros. apply MKT41 in H9; eauto.
      rewrite H9; auto. }
    pose proof H9. rewrite H7,<-H8 in H10.
    apply AxiomII in H9 as [_[_]]. unfold PreimageSet in H9.
    apply AxiomII in H10 as [_[_]]. unfold PreimageSet in H10.
    assert ((\{ λ u, u ∈ dom(f) /\ f[u] ∈ [n] \}
      ∩ \{ λ u, u ∈ dom(g) /\ g[u] ∈ [n] \})
       ⊂ \{ λ u, u ∈ ω /\ f[u] = g[u] \}).
    { assert (ω <> Φ). apply NEexE; eauto.
      apply (Const_is_Function _ n) in H11 as [H11[]]; eauto.
      assert (ran(Const n) ⊂ ω).
      { unfold Included; intros. rewrite H13 in H14.
        apply MKT41 in H14; eauto. rewrite H14; auto. }
      assert (∀ m, m ∈ ω -> (Const n)[m] = n).
      { intros. rewrite <-H12 in H15.
        apply Property_Value,Property_ran in H15; auto.
        rewrite H13 in H15. apply MKT41 in H15; eauto. }
      unfold Included; intros. apply MKT4' in H16 as [].
      apply AxiomII in H16 as [_[]]. apply AxiomII in H17 as [_[]].
      apply MKT41 in H18,H19; eauto. rewrite H2 in H16.
      apply AxiomII; repeat split; eauto. rewrite H18,H19; auto. }
    assert (\{ λ u, u ∈ ω /\ f[u] = g[u] \} ∈ F0).
    { apply AxiomII in H as [_[[_[_[_[]]]]_]].
      apply H12 in H11; auto. unfold Included; intros.
      apply AxiomII in H13; tauto. }
    destruct H0,H1. repeat split; auto. }
  intros. destruct H7 as [n[H7[]]]; eauto. rewrite H8 in H9; eauto.
Qed.

Lemma Existence_of_NPAUF_Lemma2 :
  ∀ F0 f g, F0 ∈ βω -> Function f -> Function g
  -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
  -> (∃ A, A ⊂ ω /\ Finite A /\ (f⁻¹「g「A」」 ∈ F0
    \/ g⁻¹「f「A」」 ∈ F0)) -> f〈F0〉 = g〈F0〉 -> f =_F0 g.
Proof.
  assert (∀ F0 f g, F0 ∈ βω -> Function f -> Function g
    -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
    -> (∃ A, A ⊂ ω /\ Finite A /\ f⁻¹「g「A」」 ∈ F0)
    -> f〈F0〉 = g〈F0〉 -> f =_F0 g).
  { intros. destruct H6 as [A[H6[]]].
    assert (g「 A 」 ∈ f〈 F0 〉).
    { assert (g「 A 」 ⊂ ω).
      { unfold Included; intros. apply AxiomII in H10 as [_[x[]]].
        apply H6 in H11. rewrite <-H3 in H11. apply Property_Value,
        Property_ran in H11; auto. rewrite H10; auto. }
      apply AxiomII; split; auto. apply (MKT33 ω); auto.
      pose proof MKT138; eauto. }
    assert (Finite (g「 A 」)).
    { assert (Function (g|(A)) /\ dom(g|(A)) = A
        /\ ran(g|(A)) = g「 A 」) as [H11[]].
      { pose proof H1. apply (MKT126a g A) in H11.
        pose proof H1. apply (MKT126b g A) in H12.
        split; auto. apply MKT30 in H6. rewrite H3,H6 in H12.
        split; auto. apply AxiomI; split; intros.
        - apply AxiomII; split; eauto. apply Einr in H13 as [x[]];
          auto. pose proof H13. rewrite H12 in H13.
          apply MKT126c in H15; auto. rewrite H15 in H14. eauto.
        - apply AxiomII in H13 as [H13[x[]]]. rewrite <-H12 in H15.
          pose proof H15. apply Property_Value,Property_ran in H15;
          auto. rewrite MKT126c in H15; auto. rewrite H14; auto. }
      apply MKT160 in H11. rewrite H12,H13 in H11. destruct H11.
      pose proof MKT138. apply AxiomII in H14 as [_[_]].
      eapply H14; eauto. unfold Finite. rewrite H11; auto.
      apply (MKT33 g). apply MKT75; auto. rewrite H3.
      pose proof MKT138; eauto. unfold Included; intros.
      apply MKT4' in H14; tauto. }
    assert (f〈 F0 〉 ∈ βω). { apply (FT4 F0 f ω ω); auto. New MKT138. eauto. }
    assert (~ free_ultraFilter (f〈 F0 〉) ω).
    { intro. apply (free_ultraFilter_P1 (f〈F0〉) ω H13) in H10; auto. }
    apply FT2_b in H13 as [n[]]. apply Existence_of_NPAUF_Lemma1;
    eauto. apply AxiomII in H12; tauto. }
  intros. destruct H7 as [A[H7[H9[]]]]; eauto. symmetry in H8.
  apply H in H8; eauto. destruct H8 as [_[_[_[_[_[_[_]]]]]]].
  split; auto. split; auto. repeat split; auto.
  assert (\{ λ u, u ∈ ω /\ g[u] = f[u] \}
    = \{ λ u, u ∈ ω /\ f[u] = g[u] \}).
  { apply AxiomI; split; intros; apply AxiomII in H11 as [H11[]];
    apply AxiomII; repeat split; eauto. }
  rewrite <-H11; auto.
Qed.

Lemma Existence_of_NPAUF_Lemma3 :
  ∀ F0 f g, F0 ∈ βω -> Function f -> Function g
  -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
  -> (∃ A, A ∈ F0 /\ f「A」 ∩ g「A」 = Φ) -> f〈F0〉 <> g〈F0〉.
Proof.
  intros. destruct H6 as [A[]]. intro.
  assert (A ⊂ ω).
  { apply AxiomII in H as [_[[]_]]. apply H,AxiomII in H6; tauto. }
  assert (f「 A 」 ⊂ ω /\ g「 A 」 ⊂ ω) as [].
  { split; unfold Included; intros; apply AxiomII in H10 as [_[x[]]];
    apply H9 in H11; [rewrite <-H2 in H11|rewrite <-H3 in H11];
    apply Property_Value,Property_ran in H11; auto; rewrite <-H10
    in H11; auto. }
  assert (Ensemble (f「 A 」) /\ Ensemble (g「 A 」)) as [].
  { pose proof MKT138. split; apply (MKT33 ω); eauto. }
  assert (f「 A 」 ∈ f〈 F0 〉 /\ g「 A 」 ∈ g〈 F0 〉) as [].
  { apply AxiomII in H as [_[[_[_[_[_]]]]_]].
    split; apply AxiomII; repeat split; auto. rewrite <-H2 in H9.
    pose proof H9. apply ImageSet_Property6 in H14. apply H in H14;
    auto. unfold Included; intros. apply AxiomII in H15 as [_[]].
    rewrite <-H2; auto. rewrite <-H3 in H9. pose proof H9.
    apply ImageSet_Property6 in H14. apply H in H14; auto.
    unfold Included; intros. apply AxiomII in H15 as [_[]].
    rewrite <-H3; auto. }
  assert (g〈 F0 〉 ∈ βω). { eapply FT4; eauto. New MKT138; eauto. }
  apply AxiomII in H16 as [_[[_[H16[_[]]]]_]]. elim H16.
  rewrite H8 in H14. rewrite <-H7; auto.
Qed.

Lemma Existence_of_NPAUF_Lemma4a :
  ∀ f h g, Function f -> Ordinal dom(f)
  -> (∀ u, u ∈ dom(f) -> f[u] = g[[u,f|(u)]])
  -> Function h -> Ordinal dom(h)
  -> (∀ u, u ∈ dom(h) -> h[u] = g[[u,h|(u)]])
  -> h ⊂ f \/ f ⊂ h.
Proof.
  intros. TF (∀ a, a ∈ (dom(f) ∩ dom(h)) -> f[a] = h[a]).
  - destruct (MKT109 H3 H0); apply le97 in H6; auto.
    rewrite MKT6'; auto; intros. symmetry; auto.
  - assert (∃ u, FirstMember u E \{λ a, a ∈ dom(f) ∩ dom(h)
      /\ f[a] <> h[a]\}).
    { apply (MKT107 MKT113a); red; intros.
      - appA2H H6. destruct H7. deHin. appA2G. eapply MKT111; eauto.
      - apply H5; intros. Absurd. feine a. rewrite <-H6; appA2G. }
    destruct H6 as [u []]. appA2H H6. destruct H8. deHin. elim H9.
    assert (f|(u) = h|(u)).
    { eqext; appA2H H11; destruct H12.
      - appA2G; split; auto; rewrite MKT70 in H12; auto.
        PP H12 a b. rewrite MKT70; auto. appoA2G. Absurd.
        appoA2H H13. destruct H15. elim (H7 a); try appoA2G.
        appA2G; split; auto. deGin; [eapply H0|eapply H3]; eauto.
      - appA2G; split; auto; rewrite MKT70 in H12; auto.
        PP H12 a b. rewrite MKT70; auto. appoA2G. Absurd.
        appoA2H H13. destruct H15. elim (H7 a); try appoA2G.
        appA2G; split; auto. deGin; [eapply H0|eapply H3]; eauto. }
    rewrite H1,H4,H11; auto.
Qed.

(* a special infinite recursion function of two variables,
   the proof idea is similar to MKT128 *)
Lemma Existence_of_NPAUF_Lemma4b : ∀ g,
  (∀ h x y, Function h -> Ordinal dom(h) -> x ∈ y
  -> (∀ z, z ∈ dom(h) -> h[z] = g[[z,h|(z)]])
  -> Ensemble g[[y,h|(y)]] -> Ensemble g[[x,h|(x)]])
  -> ∃ f, Function f /\ Ordinal dom(f)
    /\ (∀ x, x ∈ R -> f[x] = g[[x,f|(x)]]).
Proof.
  intros g Ha. set (f := \{\ λ u v, u ∈ R
    /\ (∃ h, Function h /\ Ordinal dom(h)
    /\ (∀ z, z ∈ dom(h) -> h[z] = g[[z,h|(z)]])
    /\ [u,v] ∈ h ) \}\).
  assert (Function f).
  { split; [unfold f; auto|]; intros. appoA2H H. appoA2H H0.
    destruct H1 as [? [h1]], H2 as [? [h2]]. deand.
    destruct (Existence_of_NPAUF_Lemma4a h1 h2 g); auto;
    [eapply H3|eapply H4]; eauto. }
  assert (Ordinal dom(f)).
  { apply MKT114; unfold rSection; deandG; intros.
    - red; intros. appA2H H0. destruct H1. appoA2H H1; tauto.
    - apply MKT107,MKT113a.
    - appA2H H1. destruct H3. appoA2H H3. destruct H4 as [? [h]].
      deand. apply Property_dom in H8. appoA2H H2.
      eapply H6 in H9; eauto. apply Property_Value in H9; auto.
      appA2G. exists h[u]. appoA2G. split; eauto. }
  assert (K1: ∀ x, x ∈ dom(f) -> f[x] = g[[x,f|(x)]]); intros.
  { appA2H H1. destruct H2. appoA2H H2.
    destruct H3 as [? [h]]. deand.
    assert (h ⊂ f); try red; intros.
    { New H8. rewrite MKT70 in H8; auto. PP H8 a b. New H9.
      apply Property_dom in H9. apply MKT111 in H9; auto.
      appoA2G; split; [appA2G;ope|eauto]. }
    apply Property_dom in H7. rewrite <-(subval H8),H6; auto.
    f_equal. apply MKT55; auto. apply MKT75. apply MKT126a; auto.
    rewrite MKT126b; auto. apply (MKT33 x); auto. unfold Included;
    intros. apply MKT4' in H9; tauto. split; auto.
    eqext; appA2H H9; destruct H10; appA2G; split; auto.
    New H10. apply H in H10 as [? []]. subst. appoA2H H11.
    destruct H11. eapply H5 in H11; eauto.
    rewrite MKT70 in H12; auto. appoA2H H12. subst.
    erewrite <-subval; eauto. apply Property_Value; auto. }
  exists f. deandG; auto. intros. TF(x ∈ dom(f)); auto.
  assert (∃ y, FirstMember y E (R ~ dom(f))) as [y[]].
  { apply (MKT107 MKT113a); red; intros. appA2H H3; tauto.
    feine x. rewrite <-H3. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. }
  pose proof H2. apply MKT69a in H5. rewrite H5. symmetry.
  apply MKT69a. intro. apply MKT69b,MKT19 in H6.
  assert (Ensemble g[[y,f|(y)]]).
  { assert (Ordinal x /\ Ordinal y) as [].
    { apply MKT4' in H3 as []. apply AxiomII in H1 as [_].
      apply AxiomII in H3 as [_]; auto. }
    pose proof H7. apply (@ MKT110 y) in H9 as [H9|[|]]; auto.
    apply (Ha f) in H9; auto. assert (x ∈ (R ~ dom(f))).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto. }
    apply H4 in H10. elim H10. apply AxiomII'; split; auto.
    apply MKT49a; eauto. rewrite H9; auto. }
  set (h := f ∪ [[y,g[[y,f|(y)]]]]).
  assert (Function h).
  { split; unfold Relation; intros. apply MKT4 in H8 as [].
    apply AxiomII in H8 as [H8[x0[y0[]]]]; eauto.
    apply MKT41 in H8; eauto. apply MKT4 in H8,H9.
    destruct H8,H9. destruct H. apply (H10 x0); auto.
    apply Property_dom in H8. assert (Ensemble ([x0,z])); eauto.
    apply MKT41 in H9; eauto. apply MKT55 in H9 as []; eauto.
    rewrite H9 in H8. apply MKT4' in H3 as []. apply AxiomII
    in H12 as []. elim H13; auto. apply MKT49b in H10; tauto.
    assert (Ensemble ([x0,y0])); eauto. apply MKT41 in H8; eauto.
    apply MKT49b in H10 as []. apply MKT55 in H8 as []; auto.
    apply Property_dom in H9. rewrite H8 in H9. apply MKT4' in H3
    as []. apply AxiomII in H13 as []. elim H14; auto.
    assert (Ensemble ([x0,y0]) /\ Ensemble ([x0,z])). split; eauto.
    destruct H10. apply MKT49b in H10,H11. destruct H10,H11.
    apply MKT41 in H8,H9; eauto. apply MKT55 in H8,H9; auto.
    destruct H8,H9. rewrite H14,H15; auto. }
  assert (dom(h) = dom(f) ∪ [y]).
  { apply AxiomI; split; intros.
    - apply AxiomII in H9 as [H9[]]. apply MKT4. apply MKT4 in H10
      as []. apply Property_dom in H10; auto.
      assert (Ensemble ([z,x0])); eauto. apply MKT49b in H11 as [_].
      apply MKT41 in H10; eauto. apply MKT55 in H10 as []; auto.
      right. rewrite H10. apply MKT41; eauto.
    - apply MKT4 in H9 as []. apply AxiomII in H9 as [H9[]].
      apply AxiomII; split; auto. exists x0. apply MKT4; auto.
      apply MKT41 in H9; eauto. rewrite H9. apply AxiomII; split.
      eauto. exists (g[[y,f|(y)]]). apply MKT4; right.
      apply MKT41; eauto. }
  assert (dom(f) ∈ y \/ dom(f) = y).
  { apply MKT4' in H3 as []. apply AxiomII in H10 as [].
    apply AxiomII in H3 as [_]. apply (@ MKT110 y) in H0
    as [H0|[|]]; auto. elim H11; auto. }
  assert (Ordinal dom(h)).
  { assert (Ordinal y).
    { apply MKT4' in H3 as []. apply AxiomII in H3; tauto. }
    split; unfold Connect; unfold Full; intros.
    - assert (Ordinal u /\ Ordinal v) as [].
      { rewrite H9 in H12,H13. apply MKT4 in H12,H13.
        destruct H12,H13. apply MKT111 in H12,H13; auto.
        apply MKT111 in H12; auto. apply MKT41 in H13; eauto.
        rewrite H13; auto. apply MKT111 in H13; auto.
        apply MKT41 in H12; eauto. rewrite H12; auto.
        apply MKT41 in H12,H13; eauto. rewrite H12,H13; auto. }
      apply (@ MKT110 u) in H15 as [H15|[|]]; auto.
      left. apply AxiomII'; split; auto. apply MKT49a; eauto.
      right; left. apply AxiomII'; split; auto. apply MKT49a; eauto.
    - unfold Included; intros. rewrite H9 in *. apply MKT4 in H12
      as []. destruct H0. apply H14 in H12. apply MKT4; auto.
      apply MKT41 in H12; eauto. rewrite H12 in H13.
      apply MKT4; left. apply NNPP; intro.
      assert (z ∈ (R ~ dom(f))).
      { apply MKT4'; split. apply AxiomII; split; eauto.
        apply MKT111 in H13; auto. apply AxiomII; split; eauto. }
      apply H4 in H15. elim H15. apply AxiomII'; split; auto.
      apply MKT49a; eauto. }
  assert (∀ x, x ∈ dom(h) -> h[x] = g[[x,h|(x)]]).
  { intros. rewrite H9 in H12.
    assert (h|(x0) = f|(x0)).
    { apply AxiomI; split; intros.
      - apply MKT4' in H13 as []. apply MKT4 in H13 as [].
        apply MKT4'; auto. apply MKT41 in H13; eauto.
        rewrite H13 in H14. apply AxiomII' in H14 as [_[]].
        apply MKT4 in H12 as []. destruct H0. apply H16 in H12.
        apply H12 in H14. apply MKT4' in H3 as [_].
        apply AxiomII in H3 as [_]. elim H3; auto.
        apply MKT41 in H12; eauto. rewrite H12 in H14.
        elim (MKT101 y); auto.
      - apply MKT4' in H13 as []. apply MKT4'; split; auto.
        apply MKT4; auto. }
    apply MKT4 in H12 as []. pose proof H12.
    apply Property_Value in H12; auto.
    assert ([x0,f[x0]] ∈ h). { apply MKT4; auto. }
    apply Property_Fun in H15; auto. rewrite <-H15,H13; auto.
    apply MKT41 in H12; eauto.
    assert ([y,g[[y,f|(y)]]] ∈ h).
    { apply MKT4; right. apply MKT41; eauto. }
    apply Property_Fun in H14; auto. rewrite H13,H12; auto. }
  assert (h ⊂ f).
  { unfold Included; intros. apply AxiomII; split; eauto.
    pose proof H13. rewrite MKT70 in H13; auto.
    apply AxiomII in H13 as [_[x0[y0[]]]]. rewrite H13 in H14.
    exists x0,y0. repeat split; eauto. apply Property_dom in H14.
    pose proof H14. apply MKT111 in H14; auto.
    apply AxiomII; split; eauto. }
  assert ([y,g[[y,f|(y)]]] ∈ h).
  { apply MKT4; right. apply MKT41; eauto. }
  apply H13,Property_dom in H14. apply MKT4' in H3 as [_].
  apply AxiomII in H3 as []; auto.
Qed.

(* if intersection is closed in A, so is the finite intersection is closed in A *)
Lemma Existence_of_NPAUF_Lemma5 :
  ∀ A B, (∀ a b, a ∈ A -> b ∈ A -> (a ∩ b) ∈ A)
  -> B ⊂ A -> Finite B -> B <> Φ -> ∩B ∈ A.
Proof.
  intros. set (p := fun n => ∀ B, B ⊂ A -> B <> Φ -> P[B] = n
    -> ∩B ∈ A).
  assert (∀ n, n ∈ ω -> p n).
  { apply Mathematical_Induction; unfold p; intros.
    - apply carE in H5. elim H4; auto.
    - assert (Finite B0).
      { unfold Finite. rewrite H7. apply MKT134; auto. }
      apply Property_Finite in H8.
      apply Inf_P7_Lemma in H7 as [B1[b[H7[H9[H10[]]]]]]; auto.
      assert (∩B0 = (∩B1) ∩ b).
      { apply AxiomI; split; intros. apply AxiomII in H13 as [].
        apply MKT4'; split; [apply AxiomII; split; auto; intros| ];
        apply H14. rewrite H12; apply MKT4; auto. rewrite H12.
        apply MKT4. right. apply MKT41; auto.
        apply AxiomII in H13 as [H13[]]. apply AxiomII in H14 as [].
        apply AxiomII; split; auto; intros. rewrite H12 in H17.
        apply MKT4 in H17 as []. apply H16; auto.
        apply MKT41 in H17; auto. rewrite H17; auto. }
      assert (b ∈ A).
      { apply H5. rewrite H12. apply MKT4; auto. }
      destruct (classic (B1 = Φ)). rewrite H15,MKT24,MKT6',MKT20'
      in H13. rewrite H13; auto. rewrite H13. apply H; auto.
      apply H4; auto. unfold Included; intros.
      apply H5. rewrite H12; apply MKT4; auto. }
  apply H3 in H1. apply H1; auto.
Qed.

(* a non-empty subset of an ordinal has a last member  *)
Lemma Existence_of_NPAUF_Lemma6 : ∀ A B, Ordinal A -> B ⊂ A
  -> Finite B -> B <> Φ -> ∃ y, LastMember y E B.
Proof.
  intros. set (p := fun n => ∀ B, B ⊂ A -> P[B] = n -> B <> Φ
    -> ∃ y, LastMember y E B).
  assert (∀ n, n ∈ ω -> p n).
  { apply Mathematical_Induction; unfold p; intros.
    - apply carE in H4. elim H5; auto.
    - assert (Finite B0).
      { unfold Finite. rewrite H6. apply MKT134; auto. }
      apply Property_Finite in H8.
      apply Inf_P7_Lemma in H6 as [B1[b[J1[H11[H6[]]]]]]; auto.
      destruct (classic (B1 = Φ)).
      + rewrite H12,MKT17 in H10. exists b. rewrite H10.
        split; auto. intros. apply MKT41 in H13; auto.
        intro. apply AxiomII' in H14 as []. apply AxiomII' in H15
        as []. rewrite H13 in H16. elim (MKT101 b); auto.
      + assert (B1 ⊂ A).
        { unfold Included; intros. apply H5.
          rewrite H10. apply MKT4; auto. }
        apply H4 in H6 as [y[]]; auto.
        assert (Ordinal y /\ Ordinal b) as [].
        { assert (b ∈ B0). { rewrite H10. apply MKT4; auto. }
          apply H5 in H15. apply H13 in H6.
          apply MKT111 in H6,H15; auto. }
        apply (@ MKT110 b) in H15 as [H15|[|]]; auto; clear H16.
        * exists y. split. rewrite H10. apply MKT4; auto.
          intros. intro. rewrite H10 in H16.
          apply MKT4 in H16 as []. apply H14 in H16; auto.
          apply MKT41 in H16; auto. apply AxiomII' in H17 as [_].
          apply AxiomII' in H17 as [_]. rewrite H16 in H17.
          elim (@ MKT102 y b); auto.
        * exists b. split; intros. rewrite H10. apply MKT4; auto.
          intro. rewrite H10 in H16. apply MKT4 in H16 as [].
          apply AxiomII' in H17 as [_]. apply AxiomII' in H17 as [_].
          assert (Ordinal y0). { apply H13,MKT111 in H16; auto. }
          destruct H18. apply H19 in H17. apply H17 in H15.
          pose proof H16. apply H14 in H20. elim H20.
          apply AxiomII'; split. apply MKT49a; eauto.
          apply AxiomII'; split; auto. apply MKT49a; eauto.
          apply MKT41 in H16; auto. apply AxiomII' in H17 as [_].
          apply AxiomII' in H17 as [_]. rewrite H16 in H17.
          elim (@ MKT101 b); auto.
        * elim H9. rewrite H15; auto. }
  apply H3 in H1. apply H1; auto.
Qed.

Lemma Existence_of_NPAUF_Lemma7 : ∀ B f g, P[B] ∈ ω \/ P[B] = ω
  -> FilterBase B ω -> Fσ ⊂ B -> Function f -> Function g
  -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
  -> \{ λ u, u ∈ ω /\ f[u] <> g[u] \} ∈ (〈B〉→ᶠ) -> (∀ A, A ⊂ ω
    -> Finite A -> (f⁻¹「g「A」」 ∪ g⁻¹「f「A」」) ∉ (〈B〉→ᶠ))
  -> (∃ a, a ⊂ ω /\ Finite_Intersection (B ∪ [a])
    /\ f「a」 ∩ g「a」 = Φ).
Proof.
  intros. pose proof MKT138. assert (Ensemble B).
  { destruct H0 as [_[]]. apply (MKT33 pow(ω)); auto.
    apply MKT38a; eauto. }
  assert (P[B] ≈ B). { apply MKT153; auto. }
  destruct H12 as [b[[][]]].
  assert (Ordinal dom(b)) as Hb.
  { rewrite H14. destruct H. apply AxiomII in H as [_[]]; auto.
    rewrite H. apply AxiomII in H10 as []; auto. }
  destruct AxiomIX as [c[]].
  set (p u v := ((∩(ran(b|(PlusOne u)))) ∩ (ω ~ ran(v))
    ∩ \{ λ u, u ∈ ω /\ f[u] <> g[u] \})
    ~ (f⁻¹「g「ran(v)」」 ∪ g⁻¹「f「ran(v)」」)).
  assert (∀ u v, Ensemble (p u v)) as Hp.
  { intros. apply (MKT33 ω); eauto. unfold Included; intros.
    apply MKT4' in H18 as [H18 _]. apply MKT4' in H18 as [_].
    apply MKT4' in H18 as [H18 _]. apply MKT4' in H18; tauto. }
  assert (∀ u v, Finite (ran(b|(PlusOne u))) -> Finite ran(v)
    -> ran(b|(PlusOne u)) <> Φ -> ran(v) ⊂ ω -> (p u v) <> Φ).
  { intros. intro. assert (((∩(ran(b|(PlusOne u)))) ∩ (ω ~ ran(v))
      ∩ \{ λ u, u ∈ ω /\ f[u] <> g[u] \}) ⊂ (f⁻¹「g「ran(v)」」
       ∪ g⁻¹「f「ran(v)」」)).
    { unfold Included; intros. apply NNPP; intro. elim (@ MKT16 z).
      rewrite <-H22. apply MKT4'; split; auto.
      apply AxiomII; split; eauto. }
    pose proof H0. destruct H0 as [H0[]].
    apply FilterBase_Property1 in H24. pose proof H24.
    apply (Filter_Extension_1_and_2 _ ω) in H27 as []; auto.
    destruct H28 as [_[_[H28[]]]]. apply H30 in H23.
    apply H9 in H19; auto. unfold Included; intros.
    apply MKT4 in H31 as []; apply AxiomII in H31 as [_[]];
    [rewrite <-H4|rewrite <-H5]; auto.
    apply H29; [ |apply H29; auto].
    assert (ran(b|(PlusOne u)) ⊂ 〈B〉→ᶠ).
    { unfold Included; intros. apply H27. rewrite <-H15.
      apply AxiomII in H31 as [H31[]]. apply MKT4' in H32 as [].
      apply Property_ran in H32; auto. }
    apply Existence_of_NPAUF_Lemma5; auto.
    assert ((ω ~ ran(v)) ⊂ ω).
    { unfold Included; intros. apply MKT4' in H31; tauto. }
    apply H27,H1. apply AxiomII; repeat split; auto.
    apply (MKT33 ω); eauto. assert (ω ~ (ω ~ ran(v)) = ran(v)).
    { apply AxiomI; split; intros. apply MKT4' in H32 as [].
      apply AxiomII in H33 as []. apply NNPP; intro. elim H34.
      apply MKT4'; split; auto. apply AxiomII; split; eauto.
      apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT4' in H33 as [].
      apply AxiomII in H34 as []; auto. }
    rewrite H32; auto. New MKT138; eauto. }
  assert (∀ u, u ∈ dom(b) -> Finite ran(b|(PlusOne u))
    /\ ran(b|(PlusOne u)) <> Φ).
  { intros. assert (dom(b|(PlusOne u)) ⊂ (PlusOne u)).
    { unfold Included; intros. apply AxiomII in H20 as [H20[]].
      apply MKT4' in H21 as []. apply AxiomII' in H22; tauto. }
    assert (Function (b|(PlusOne u))). { apply MKT126a; auto. }
    assert (Ensemble (b|(PlusOne u))).
    { apply (MKT33 b). apply MKT75; auto. apply Property_PClass
      in H11. rewrite H14; eauto. unfold Included; intros.
      apply MKT4' in H22; tauto. }
    apply MKT160 in H21; auto. apply MKT158 in H20.
    assert (u ∈ ω).
    { rewrite H14 in H19. destruct H. apply AxiomII in H10 as [_[]].
      eapply H23; eauto. rewrite <-H; auto. }
    apply MKT134 in H23. pose proof H23. apply MKT164 in H24.
    apply MKT156 in H24 as [_]. rewrite H24 in H20.
    apply AxiomII in H10 as [_[]].
    assert (P[dom(b|(PlusOne u))] ∈ ω).
    { destruct H20. eapply H25; eauto. rewrite H20; auto. }
    split. destruct H21. eapply H25; eauto. unfold Finite.
    rewrite H21; auto. apply Property_Value in H19; auto.
    assert ([u,b[u]] ∈ (b|(PlusOne u))).
    { apply MKT4'; split; auto. apply AxiomII'; repeat split;
      eauto. apply Property_dom in H19. apply MKT4; eauto.
      apply Property_ran in H19. apply MKT19; eauto. }
    intro. elim (@ MKT16 b[u]). rewrite <-H28.
    apply Property_ran in H27; auto. }
  set (k := \{\ λ u v, ∃ i j, u = [i,j] /\ i ∈ dom(b)
    /\ v = c[p i j] \}\).
  set (dk := dom(b) × \{ λ u, Finite ran(u) /\ ran(u) ⊂ ω \}).
  assert (Function k /\ dk ⊂ dom(k)) as [].
  { repeat split; unfold Included; unfold Relation; intros.
    - apply AxiomII in H20 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H20 as [H20[i1[j1[H22[]]]]].
      apply AxiomII' in H21 as [H21[i2[j2[H25[]]]]].
      rewrite H22 in H25. apply MKT49b in H20 as [].
      rewrite H22 in H20. apply MKT49b in H20 as [].
      apply MKT55 in H25 as []; auto. rewrite H24,H27,H25,H30; auto.
    - apply AxiomII in H20 as [H20[x[y[H21[]]]]].
      apply AxiomII in H23 as [H23[]]. apply AxiomII; split; auto.
      exists c[p x y]. apply AxiomII; split.
      assert ((p x y) ∈ dom(c)).
      { rewrite H17. apply MKT4'; split. apply MKT19; auto.
        apply AxiomII; split; auto. intro. apply MKT41 in H26; auto.
        apply H18 in H26; auto; apply H19; auto. }
      apply H16 in H26. apply MKT49a; eauto.
      exists z,c[p x y]. split; eauto. }
  assert (∀ u v, [u,v] ∈ dom(k) -> k[[u,v]] = c[p u v]).
  { intros. apply Property_Value,AxiomII' in H22
    as [H22[x[y[H23[]]]]]; auto. apply MKT49b in H22 as [H22 _].
    apply MKT49b in H22 as []. apply MKT55 in H23 as []; auto.
    rewrite H25,H23,H27; auto. }
  assert (∀ u v, [u,v] ∈ dom(k) -> k[[u,v]] ∈ (p u v)).
  { intros. rewrite H22; auto. pose proof H23. apply MKT69b in H23.
    apply H22 in H24. rewrite H24 in H23. apply MKT69b' in H23.
    apply H16; auto. }
  assert (∀ h, Function h -> Ordinal dom(h)
    -> (∀ x, x ∈ dom(h) -> h[x] = k[[x,h|(x)]])
    -> ran(h) ⊂ ω /\ (∀ x, x ∈ dom(b) -> [x,h|(x)] ∈ dk)).
  { intros. assert (ran(h) ⊂ ω).
    { unfold Included; intros. apply Einr in H27 as [x[]]; auto.
      pose proof  H27. apply H26 in H29. apply MKT69b in H27.
      rewrite H29 in H27. apply MKT69b',H23,AxiomII in H27 as [_[]].
      apply MKT4' in H27 as [_]. apply MKT4' in H27 as [H27 _].
      apply MKT4' in H27 as []. rewrite H28,H29; auto. }
    split; auto. intros. assert (dom(h|(x)) ⊂ x).
    { unfold Included; intros. apply AxiomII in H29 as [_[]].
      apply MKT4' in H29 as []. apply AxiomII' in H30; tauto. }
    assert (Ensemble (h|(x))).
    { apply MKT75. apply MKT126a; auto. apply (MKT33 x); eauto. }
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    apply AxiomII; split; auto. apply MKT158 in H29.
    pose proof H10. apply AxiomII in H31 as [_[_]].
    assert (x ∈ ω).
    { rewrite H14 in H28. destruct H. eapply H31; eauto.
      rewrite <-H; auto. }
    assert (P[dom(h|(x))] ∈ ω).
    { pose proof H32. apply MKT164,MKT156 in H32 as [].
      rewrite H34 in H29. destruct H29. eapply H31; eauto.
      rewrite H29; auto. }
    split. apply (MKT126a h x),MKT160 in H24 as []; auto.
    eapply H31; eauto. rewrite <-H24 in H33; auto.
    assert (ran(h|(x)) ⊂ ran(h)).
    { unfold Included; intros. apply Einr in H34 as [x1[]].
      rewrite MKT126c in H35; auto. rewrite H35.
      apply (@ Property_ran x1),Property_Value; auto.
      apply AxiomII in H34 as [_[]]. apply MKT4' in H34 as [].
      apply Property_dom in H34; auto. apply MKT126a; auto. }
    unfold Included; auto. }
  assert (∀ h x y, Function h -> Ordinal dom(h) -> x ∈ y
    -> (∀ z, z ∈ dom(h) -> h[z] = k[[z,h|(z)]])
    -> Ensemble (k[[y,h|(y)]]) -> Ensemble (k[[x,h|(x)]])).
  { intros. pose proof H25. apply H24 in H30 as []; auto.
    assert (y ∈ dom(b)).
    { apply MKT19,MKT69b',Property_Value,AxiomII' in H29
      as [H29[x0[y0[H32[]]]]]; auto. apply MKT49b in H29 as [];
      auto. apply MKT49b in H29 as []; auto.
      apply MKT55 in H32 as []; auto. rewrite H32; auto. }
    assert (x ∈ dom(b)). { destruct Hb. apply H34 in H32; auto. }
    apply H31,H21,H23 in H33; eauto. }
  apply (Existence_of_NPAUF_Lemma4b k) in H25 as [h[H25[]]].
  assert (ran(h) ⊂ ω /\ (∀ x, x ∈ dom(b) -> [x,h|(x)] ∈ dk)) as [].
  { apply H24; auto. intros. apply H27. apply AxiomII; split; eauto.
    apply MKT111 in H28; auto. }
  assert (dom(b) ⊂ dom(h)).
  { unfold Included; intros. apply NNPP; intro.
    assert (z ∈ R).
    { apply AxiomII; split; eauto. apply MKT111 in H30; auto. }
    apply H27 in H32. apply H29,H21,H23 in H30.
    apply MKT69a in H31. elim MKT39. rewrite <-H31,H32; eauto. }
  assert (∀ x, x ∈ dom(b) -> h[x] ∈ (p x (h|(x)))).
  { intros. rewrite H27; auto. apply AxiomII; split; eauto.
    apply MKT111 in H31; auto. }
  assert (∀ x, x ∈ dom(h) -> h[x] ∈ (p x (h|(x)))).
  { intros. assert (x ∈ R).
    { apply AxiomII; split; eauto. apply MKT111 in H32; auto. }
    apply H27 in H33. apply MKT69b in H32. rewrite H33 in H32.
    apply MKT69b',H23 in H32. rewrite H33; auto. }
  exists ran(h). repeat split; auto.
  - unfold Finite_Intersection; intros.
    destruct (classic (ran(h) ∈ A)).
    assert ((A ~ [ran(h)]) ⊂ A).
    { unfold Included; intros. apply MKT4' in H36; tauto. }
    assert ((A ~ [ran(h)]) ⊂ B).
    { unfold Included; intros. apply MKT4' in H37 as [].
      apply H33,MKT4 in H37 as []; auto. apply MKT41 in H37; eauto.
      apply AxiomII in H38 as []. elim H39. apply MKT41; eauto. }
    assert (Finite (A ~ [ran(h)])). { apply finsub in H36; auto. }
    assert (b⁻¹「A ~ [ran(h)]」 ⊂ dom(b)).
    { unfold Included; intros. apply AxiomII in H39; tauto. }
    assert ((b⁻¹「A ~ [ran(h)]」) ≈ (A ~ [ran(h)])).
    { exists (b|(b⁻¹「A ~ [ran(h)]」)). split. split.
      apply MKT126a; auto. split; unfold Relation; intros.
      apply AxiomII in H40 as [_[x0[y0[]]]]; eauto.
      apply AxiomII' in H40 as [_]. apply AxiomII' in H41 as [_].
      apply MKT4' in H40 as [H40 _]. apply MKT4' in H41 as [H41 _].
      pose proof H40; pose proof H41. apply Property_dom in H42,H43.
      apply Property_Fun in H40,H41; auto. rewrite H40 in H41.
      apply f11inj in H41; auto. split. rewrite MKT126b; auto.
      apply MKT30 in H39. rewrite H39; auto.
      apply AxiomI; split; intros. apply AxiomII in H40 as [H40[]].
      apply MKT4' in H41 as []. apply AxiomII' in H42 as [H42[]].
      apply AxiomII in H43 as [H43[]]. apply Property_Fun in H41;
      auto. rewrite H41; auto. apply AxiomII; split; eauto.
      pose proof H40. apply H37 in H41. rewrite <-H15 in H41.
      apply Einr in H41 as [x[]]; auto. exists x. apply MKT4';
      split. apply Property_Value in H41; auto. rewrite H42; auto.
      apply AxiomII'; repeat split; eauto. apply MKT49a; eauto.
      apply AxiomII; repeat split; eauto. rewrite <-H42; auto. }
    assert (Ensemble (b⁻¹「A ~ [ran(h)]」)
      /\ Ensemble (A ~ [ran(h)])) as [].
    { split; [apply (MKT33 dom(b))|apply (MKT33 B)]; auto.
      rewrite H14. destruct H; eauto. }
    apply MKT154 in H40; auto.
    destruct (classic (A ~ [ran(h)] = Φ)).
    assert (A = [ran(h)]).
    { apply AxiomI; split; intros. apply NNPP; intro.
      elim (@ MKT16 z). rewrite <-H43. apply MKT4'; split; auto.
      apply AxiomII; split; eauto. apply MKT41 in H44; eauto.
      rewrite H44; auto. }
    assert (Ensemble ran(h)); eauto. apply MKT44 in H45 as [H45 _].
    rewrite H44,H45. destruct H0 as [H0 _]. rewrite <-H15 in H0.
    apply NEexE in H0 as [z]. apply Einr in H0 as [x[]]; auto.
    apply H30,Property_Value,Property_ran in H0; auto.
    apply NEexE; eauto.
    assert (b⁻¹「A ~ [ran(h)]」 <> Φ).
    { apply NEexE in H43 as [y]. pose proof H43. apply H37 in H44.
      rewrite <-H15 in H44. apply Einr in H44 as [x[]]; auto.
      assert (x ∈ b⁻¹「A ~ [ran(h)]」).
      { rewrite H45 in H43. apply AxiomII; split; eauto. }
      apply NEexE; eauto. } clear H43.
    assert (∃ y, LastMember y E (b⁻¹「A ~ [ran(h)]」)).
    { apply Existence_of_NPAUF_Lemma6 in H39; auto.
      unfold Finite. rewrite H40; auto. }
    clear H44. destruct H43 as [y[]].
    assert ((A ~ [ran(h)]) ⊂ ran(b|(PlusOne y))).
    { unfold Included; intros. apply AxiomII; split; eauto.
      pose proof H45. apply H37 in H46. rewrite <-H15 in H46.
      apply Einr in H46 as [x[]]; auto.
      assert (x ∈ b⁻¹「A ~ [ran(h)]」).
      { apply AxiomII; repeat split; eauto. rewrite <-H47; auto. }
      exists x. apply MKT4'; split. apply Property_Value in H46;
      auto. rewrite H47; auto. apply AxiomII'; split.
      apply MKT49a; eauto. split; eauto. pose proof H43.
      apply AxiomII in H49 as [_[H49 _]].
      assert (Ordinal x /\ Ordinal y) as [].
      { apply MKT111 in H46,H49; auto. }
      apply (@ MKT110 x) in H51 as [H51|[|]]; auto. apply MKT4;
      auto. apply H44 in H48. elim H48. apply AxiomII'; split.
      apply MKT49a; eauto. apply AxiomII'; split; auto.
      apply MKT49a; eauto. apply MKT4; right. apply MKT41; eauto. }
    apply MKT31 in H45 as [_].
    assert (∩A = (∩(A ~ [ran(h)])) ∩ (ran(h))).
    { apply AxiomI; split; intros. apply AxiomII in H46 as [].
      apply MKT4'; split. apply AxiomII; split; intros; auto.
      apply H47; auto. apply MKT4' in H46 as [].
      apply AxiomII in H46 as []. apply AxiomII; split; auto;
      intros. destruct (classic (y0 = ran(h))). rewrite H50; auto.
      apply H48. apply MKT4'; split; auto. apply AxiomII; split;
      eauto. intro. apply MKT41 in H51; eauto. }
    assert (h[y] ∈ ∩A).
    { rewrite H46. apply MKT4'; split. apply H39,H31,MKT4' in H43
      as [H43 _]. apply MKT4' in H43 as [H43 _]; auto.
      apply H39,H30,Property_Value,Property_ran in H43; auto. }
    apply NEexE; eauto. assert (A ⊂ B).
    { unfold Included; intros. pose proof H36.
      apply H33,MKT4 in H36 as []; auto. apply MKT41 in H36.
      rewrite H36 in H37. elim H35; auto. apply (MKT33 ω); eauto. }
    apply FilterBase_Property1 in H0. apply H0 in H36; auto.
  - apply AxiomI; split; intros; elim (@ MKT16 z); auto.
    apply MKT4' in H33 as []. apply AxiomII in H33 as [H33[x1[]]].
    apply AxiomII in H34 as [H34[x2[]]].
    apply Einr in H36 as [u1[]]; auto.
    apply Einr in H38 as [u2[]]; auto.
    pose proof H36; pose proof H38. apply H32 in H41,H42.
    apply MKT4' in H41 as []. apply MKT4' in H41 as [_].
    apply MKT4' in H41 as [_]. apply AxiomII in H43 as [_].
    apply MKT4' in H42  as []. apply MKT4' in H42 as [_].
    apply MKT4' in H42 as [_]. apply AxiomII in H44 as [_].
    apply AxiomII in H41 as [_[]]. apply AxiomII in H42 as [_[]].
    assert (x1 ∈ dom(f) /\ x2 ∈ dom(g)) as [].
    { split; apply NNPP; intro; apply MKT69a in H47;
      elim MKT39; [rewrite <-H47,<-H35|rewrite <-H47,<-H37]; auto. }
    assert (Ordinal u1 /\ Ordinal u2) as [].
    { apply MKT111 in H36,H38; auto. }
    apply (@ MKT110 u2) in H49 as [H49|[|]]; auto; clear H50.
    + elim H43. apply MKT4; left. rewrite <-H39.
      apply AxiomII; repeat split; eauto. rewrite <-H35.
      apply AxiomII; split; auto. exists x2. split; auto.
      apply (@ Property_ran u2). apply MKT4'; split.
      rewrite H40. apply Property_Value; auto.
      apply AxiomII'; repeat split; eauto. apply MKT49a; eauto.
    + elim H44. apply MKT4; right. rewrite <-H40.
      apply AxiomII; repeat split; eauto. rewrite <-H37.
      apply AxiomII; split; auto. exists x1. split; auto.
      apply (@ Property_ran u1). apply MKT4'; split.
      rewrite H39. apply Property_Value; auto.
      apply AxiomII'; repeat split; eauto. apply MKT49a; eauto.
    + rewrite <-H49,<-H40 in H39. rewrite H35,<-H39 in H37.
      elim H45. rewrite <-H49,<-H40,<-H39; auto.
Qed.

Lemma Existence_of_NPAUF_Lemma8 : ∀ a, Ensemble a
  -> pow(a) ≈ \{ λ f, Function f /\ dom(f) = a /\ ran(f) ⊂ [Φ|[Φ]] \}.
Proof.
  intros. set (h b := \{\ λ u v, (u ∈ b /\ v = [Φ])
    \/ (u ∈ a ~ b /\ v = Φ) \}\).
  pose proof in_ω_0; pose proof in_ω_1.
  assert (∀ b, b ⊂ a -> Function (h b) /\ dom(h b) = a
    /\ ran(h b) ⊂ [Φ|[Φ]]).
  { intros. repeat split; unfold Relation; unfold Included; intros.
    - apply AxiomII in H3 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H3 as [_]. apply AxiomII' in H4 as [_].
      destruct H3 as [[]|[]]; destruct H4 as [[]|[]];
      rewrite H5,H6; auto; [apply MKT4' in H4 as []|
      apply MKT4' in H3 as []]; apply AxiomII in H7 as [];
      contradiction.
    - apply AxiomI; split; intros. apply AxiomII in H3 as [H3[]].
      apply AxiomII' in H4 as [_[[]|[]]]; auto.
      apply MKT4' in H4; tauto. apply AxiomII; split; eauto.
      destruct (classic (z ∈ b)). exists [Φ].
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      exists Φ. apply AxiomII'; split; auto. apply MKT49a; eauto.
    - apply AxiomII in H3 as [H3[]].
      apply AxiomII' in H4 as [_[[]|[]]];
      apply AxiomII; split; auto; [right|left]; apply MKT41; auto. }
  assert (∀ b, b ⊂ a -> Ensemble (h b)).
  { intros. apply H2 in H3 as [H3[]]. apply MKT75; auto.
    rewrite H4; auto. }
  set (g := \{\ λ u v, u ∈ pow(a) /\ v = (h u) \}\).
  exists g. repeat split; unfold Relation; unfold Included; intros.
  - apply AxiomII in H4 as [_[x[y[]]]]; eauto.
  - apply AxiomII' in H4 as [_[]]. apply AxiomII' in H5 as [_[]].
    rewrite H6,H7; auto.
  - apply AxiomII in H4 as [_[x[y[]]]]; eauto.
  - apply AxiomII' in H4 as []. apply AxiomII' in H6 as [H6[]].
    apply AxiomII' in H5 as []. apply AxiomII' in H9 as [H9[]].
    apply NNPP; intro. assert ((y ~ z) <> Φ \/ (z ~ y) <> Φ).
    { apply NNPP; intro. apply notandor in H13 as [].
      apply ->NNPP in H13. apply ->NNPP in H14. elim H12.
      apply AxiomI; split; intros; apply NNPP; intro;
      elim (@ MKT16 z0); [rewrite <-H13|rewrite <-H14];
      apply MKT4'; split; auto; apply AxiomII; split; eauto. }
    apply AxiomII in H7 as []. apply AxiomII in H10 as [].
    destruct H13; apply NEexE in H13 as [].
    + assert ([x0,[Φ]] ∈ (h y)).
      { apply AxiomII'; split. apply MKT49a; eauto.
        apply MKT4' in H13 as []; auto. }
      assert ([x0,Φ] ∈ (h z)).
      { apply AxiomII'; split. apply MKT49a; eauto. right.
        split; auto. apply MKT4' in H13 as []. apply MKT4'; auto. }
      assert (Φ = [Φ]).
      { apply H2 in H14 as [[]]. apply (H18 x0); auto.
        rewrite <-H8,H11; auto. }
      assert (Φ ∈ [Φ]). { apply MKT41; auto. }
      elim (@ MKT16 Φ). rewrite <-H18 in H19; auto.
    + assert ([x0,[Φ]] ∈ (h z)).
      { apply AxiomII'; split. apply MKT49a; eauto.
        apply MKT4' in H13 as []; auto. }
      assert ([x0,Φ] ∈ (h y)).
      { apply AxiomII'; split. apply MKT49a; eauto. right.
        split; auto. apply MKT4' in H13 as []. apply MKT4'; auto. }
      assert (Φ = [Φ]).
      { apply H2 in H14 as [[]]. apply (H18 x0); auto.
        rewrite <-H8,H11; auto. }
      assert (Φ ∈ [Φ]). { apply MKT41; auto. }
      elim (@ MKT16 Φ). rewrite <-H18 in H19; auto.
  - apply AxiomI; split; intros. apply AxiomII in H4 as [_[]].
    apply AxiomII' in H4 as [_[]]; auto. apply AxiomII; split;
    eauto. exists (h z). apply AxiomII'; split; auto.
    apply MKT49a; eauto. apply H3. apply AxiomII in H4 as []; auto.
  - apply AxiomI; split; intros. apply AxiomII in H4 as [H4[]].
    apply AxiomII; split; eauto. apply AxiomII' in H5 as [_[]].
    apply AxiomII in H5 as []. apply H2 in H7. rewrite H6; auto.
    apply AxiomII in H4 as [H4[H5[]]]. apply AxiomII; split; auto.
    exists (z⁻¹「[[Φ]]」). apply AxiomII'.
    assert (z⁻¹「[[Φ]]」 ⊂ a).
    { unfold Included; intros. apply AxiomII in H8 as [_[]].
      rewrite H6 in H8; auto. }
    assert (z⁻¹「[[Φ]]」 ∈ pow(a)).
    { apply AxiomII; split; auto. apply (MKT33 a); auto. }
    repeat split; eauto. apply MKT71; auto. apply H2; auto.
    intros. pose proof H8. apply H2 in H10 as [H10[]].
    destruct (classic (x ∈ a)).
    + destruct (classic (x ∈ z⁻¹「[[Φ]]」)).
      * rewrite <-H11 in H13. apply Property_Value in H13; auto.
        apply AxiomII' in H13 as [_[[]|[]]]. apply AxiomII in H14
        as [_[]]. apply MKT41 in H16; auto. rewrite H15,H16; auto.
        apply MKT4' in H13 as []. apply AxiomII in H16 as [].
        elim H17; auto.
      * rewrite <-H11 in H13. apply Property_Value in H13; auto.
        apply AxiomII' in H13 as [_[[]|[]]]. elim H14; auto.
        clear H14. pose proof H13. apply MKT4' in H14 as [H14 _].
        rewrite <-H6 in H14. apply Property_Value,Property_ran,H7
        in H14; auto. apply AxiomII in H14 as [_[]].
        apply MKT41 in H14; auto. rewrite H14,H15; auto.
        apply MKT4' in H13 as []. apply AxiomII in H16 as [].
        elim H17. rewrite <-H6 in H13. apply AxiomII; auto.
    + pose proof H13. rewrite <-H6 in H13. rewrite <-H11 in H14.
      apply MKT69a in H13,H14. rewrite H13,H14; auto.
Qed.

Lemma Existence_of_NPAUF_Lemma9 : ∀ x y, x ≈ y -> Ensemble x
  -> pow(x) ≈ pow(y).
Proof.
  intros. pose proof H. apply MKT146,eqvp in H; auto.
  destruct H1 as [f[[][]]].
  set (h := \{\ λ u v, u ∈ pow(x) /\ v = f「u」 \}\).
  exists h. repeat split; unfold Relation; intros.
  - apply AxiomII in H5 as [_[a[b[]]]]; eauto.
  - apply AxiomII' in H5 as [_[]]. apply AxiomII' in H6 as [_[]].
    rewrite H7,H8; auto.
  - apply AxiomII in H5 as [_[a[b[]]]]; eauto.
  - apply AxiomII' in H5 as []. apply AxiomII' in H7 as [H7[]].
    apply AxiomII' in H6 as []. apply AxiomII' in H10 as [H10[]].
    apply AxiomII in H8 as []. apply AxiomII in H11 as [].
    assert (f⁻¹「f「y0」」 = f⁻¹「f「z」」).
    { rewrite <-H9,<-H12; auto. }
    rewrite <-ImageSet_Property7,<-ImageSet_Property7 in H15;
    try rewrite H3; auto; split; auto.
  - apply AxiomI; split; intros. apply AxiomII in H5 as [H5[]].
    apply AxiomII' in H6; tauto. apply AxiomII; split; eauto.
    exists (f「z」). apply AxiomII'; split; auto.
    apply MKT49a; eauto. apply (MKT33 y); auto.
    unfold Included; intros. apply AxiomII in H6 as [_[x0[]]].
    apply AxiomII in H5 as []. rewrite <-H3 in H8.
    apply H8,Property_Value,Property_ran in H7; auto.
    rewrite H4,<-H6 in H7; auto.
  - apply AxiomI; split; intros. apply AxiomII in H5 as [H5[]].
    apply AxiomII' in H6 as [_[]]. apply AxiomII; split; auto.
    unfold Included; intros. rewrite H7 in H8.
    apply AxiomII in H8 as [_[x1[]]]. apply AxiomII in H6 as [_].
    rewrite <-H3 in H6. apply H6,Property_Value,Property_ran in H9;
    auto. rewrite <-H8,H4 in H9; auto. apply AxiomII in H5 as [].
    apply AxiomII; split; eauto. exists (f⁻¹「z」).
    assert (f⁻¹「z」⊂ x).
    { unfold Included; intros. apply AxiomII in H7 as [_[]].
      rewrite H3 in H7; auto. }
    assert (f⁻¹「z」∈ pow(x)).
    { apply AxiomII; split; auto. apply (MKT33 x); auto. }
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    rewrite ImageSet_Property8_b; auto. rewrite H4; auto.
Qed.

Lemma Existence_of_NPAUF_Lemma10 :
  \{ λ f, Function f /\ dom(f) = ω /\ ran(f) ⊂ ω \} ≈ pow(ω).
Proof.
  assert (Ensemble ω). { pose proof MKT165. eauto. }
  assert (Ensemble (ω × ω)). { apply MKT74; auto. }
  assert (Ensemble (pow(ω))). { apply MKT38a; auto. }
  assert (\{ λ f, Function f /\ dom(f) = ω /\ ran(f) ⊂ [Φ|[Φ]] \}
    ⊂ \{ λ f, Function f /\ dom(f) = ω /\ ran(f) ⊂ ω \}).
  { unfold Included; intros. apply AxiomII in H2 as [H2[H3[]]].
    apply AxiomII; repeat split; destruct H3; auto.
    intros. apply H5 in H7. apply AxiomII in H7 as [_[]];
    apply MKT41 in H7; auto; rewrite H7; auto. apply in_ω_1. }
  assert (\{ λ f, Function f /\ dom(f) = ω /\ ran(f) ⊂ ω \}
    ⊂ pow(ω × ω)).
  { unfold Included; intros. apply AxiomII in H3 as [H3[H4[]]].
    apply AxiomII; split; auto. unfold Included; intros.
    pose proof H7. rewrite MKT70 in H7; auto.
    apply AxiomII in H7 as [H7[x[y[H9 _]]]].
    rewrite H9 in H8. pose proof H8. apply Property_dom in H8.
    apply Property_ran,H6 in H10. rewrite H5 in H8.
    rewrite H9 in *. apply AxiomII'; auto. }
  assert (pow(ω × ω) ≈ pow(ω)).
  { apply Existence_of_NPAUF_Lemma9; auto. apply MKT154; auto.
    pose proof MKT165. apply MKT156 in H4 as [].
    rewrite H5. apply MKT179. apply MKT4'; split.
    apply MKT165. apply AxiomII; split; auto. apply MKT101. }
  assert (Ensemble (pow(ω × ω))). { apply eqvp in H4; auto. }
  pose proof H. apply Existence_of_NPAUF_Lemma8,MKT146 in H6.
  assert (Ensemble (\{ λ f, Function f /\ dom(f) = ω
    /\ ran(f) ⊂ [Φ|[Φ]] \})). { apply eqvp in H6; auto. }
  assert (Ensemble (\{ λ f, Function f /\ dom(f) = ω
    /\ ran(f) ⊂ ω \})). { apply (MKT33 (pow(ω × ω))); auto. }
  apply MKT158 in H2,H3. apply MKT154 in H4,H6; auto.
  rewrite H6 in H2. rewrite H4 in H3. apply MKT154; auto.
  destruct H2,H3; try rewrite H2; try rewrite H3; auto.
  elim (MKT102 (P[pow(ω)]) (P[\{ λ f, Function f /\ dom(f) = ω
    /\ ran(f) ⊂ ω \}])); auto.
Qed.

Lemma Existence_of_NPAUF_Lemma11 :
  \{ λ f, Function f /\ dom(f) = ω /\ ran(f) ⊂ ω \}
    × \{ λ f, Function f /\ dom(f) = ω /\ ran(f) ⊂ ω \} ≈ pow(ω).
Proof.
  pose proof Existence_of_NPAUF_Lemma10.
  assert (Ensemble (pow(ω))).
  { apply MKT38a. pose proof MKT165. eauto. }
  pose proof H. apply eqvp in H1; auto.
  assert (P[pow(ω)] ∈ (C ~ ω)).
  { assert (P[pow(ω)] ∈ C). { apply Property_PClass; auto. }
    apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. assert (Ensemble ω). { pose proof MKT165; eauto. }
    apply MKT161 in H4. pose proof MKT165. apply MKT156 in H5 as [].
    rewrite H6 in H4. elim (MKT102 P[pow(ω)] ω); auto. }
  apply MKT179 in H2. apply MKT154 in H; auto.
  rewrite <-H,<-lem179a,H in H2; auto.
  apply MKT154; auto. apply MKT74; auto.
Qed.

Lemma Existence_of_NPAUF_Lemma12 : ∀ n, n ∈ R
  -> LastMember n E (PlusOne n).
Proof.
  intros. split. apply MKT4; right. apply MKT41; eauto.
  intros. intro. apply AxiomII' in H1 as [].
  apply AxiomII' in H2 as []. apply MKT4 in H0 as [].
  elim (MKT102 n y); auto. apply MKT41 in H0; eauto.
  rewrite H0 in H3. elim (MKT101 n); auto.
Qed.

Lemma Existence_of_NPAUF_Lemma13 : ∀ n, n ∈ P[pow(ω)]
  -> (PlusOne n) ∈ P[pow(ω)].
Proof.
  intros. pose proof MKT165.
  assert (Ensemble pow(ω)). { apply MKT38a; eauto. }
  pose proof H1. apply Property_PClass in H2.
  pose proof H2. apply AxiomII in H3 as [_[H3 _]].
  apply AxiomII in H3 as []. pose proof H. apply MKT111 in H5; auto.
  assert ((PlusOne n) ∈ R).
  { assert (n ∈ R). { apply AxiomII; split; eauto. }
    apply MKT123 in H6 as []. apply AxiomII in H6; tauto. }
  apply AxiomII in H6 as []. pose proof H7.
  apply (@ MKT110 P[pow(ω)]) in H8 as [H8|[|]]; auto.
  - apply MKT4 in H8 as []. elim (MKT102 n P[pow(ω)]); auto.
    apply MKT41 in H8; eauto. rewrite H8 in H.
    elim (MKT101 n); auto.
  - pose proof H0. apply AxiomII in H9 as [H9 _].
    apply MKT161 in H9. pose proof H0. apply MKT156 in H10 as [_].
    rewrite H10,H8 in H9. apply MKT4 in H9.
    assert (n ∈ (R ~ ω)).
    { apply MKT4'; split. apply AxiomII; split; eauto.
      apply AxiomII; split; eauto. intro. destruct H9.
      elim (MKT102 n ω); auto. apply MKT41 in H9; eauto.
      rewrite H9 in H11. elim (MKT101 n); auto. }
    apply MKT174 in H11. pose proof H2. rewrite H8 in H12.
    apply MKT156 in H12 as [_]. rewrite <-H12,H11 in H8.
    apply MKT154 in H8; eauto. apply MKT153,(MKT147 _ _ n) in H1;
    auto. apply AxiomII in H2 as [_[]]. apply H13 in H.
    elim H; auto. apply AxiomII; split; eauto.
Qed.

Lemma Existence_of_NPAUF_Lemma14 : ∀ A, P[A] = ω
  -> (∀ a, a ∈ A -> P[a] = ω) -> P[∪A] = ω.
Proof.
  intros. assert (Ensemble ω). { pose proof MKT138; eauto. }
  assert (Ensemble A).
  { apply MKT19. apply NNPP; intro. rewrite <-MKT152b in H2.
    apply MKT69a in H2. rewrite <-H,H2 in H1. elim MKT39; auto. }
  pose proof MKT165. apply MKT156 in H3 as [_].
  assert (ω ≈ A). { apply MKT154; auto. rewrite H3; auto. }
  destruct H4 as [fA[[][]]].
  assert (∀ n, n ∈ ω -> ω ≈ fA[n]).
  { intros. rewrite <-H6 in H8. apply Property_Value,Property_ran
    in H8; auto. rewrite H7 in H8. pose proof H8. apply H0 in H9.
    rewrite <-H3 in H9. symmetry in H9. apply MKT154 in H9; eauto. }
  destruct AxiomIX as [c[]].
  set (g n := c[\{ λ f, Function1_1 f /\ dom(f) = ω
    /\ ran(f) = fA[n] \}]).
  assert (∀ n, n ∈ ω -> Function1_1 (g n) /\ dom(g n) = ω
    /\ ran(g n) = fA[n]).
  { intros. assert (\{ λ f, Function1_1 f /\ dom(f) = ω
      /\ ran(f) = fA[n] \} ∈ dom(c)).
    { assert (Ensemble (\{ λ f, Function1_1 f /\ dom(f) = ω
        /\ ran(f) = fA[n] \})).
      { apply (MKT33 (pow(ω × (fA[n])))). apply MKT38a.
        apply MKT74; auto. rewrite <-H6 in H11.
        apply Property_Value,Property_ran in H11; eauto.
        unfold Included; intros. apply AxiomII; split; eauto.
        apply AxiomII in H12 as [H12[H13[]]]. rewrite <-H14,<-H15.
        unfold Included; intros. pose proof H16.
        rewrite MKT70 in H17. apply AxiomII in H17
        as [H17[x[y[]]]]. rewrite H18 in *.
        apply AxiomII'; repeat split; auto.
        apply Property_dom in H16; auto.
        apply Property_ran in H16; auto. destruct H13; auto. }
      rewrite H10. apply MKT4'; split. apply MKT19; auto.
      apply AxiomII; split; auto. intro. apply MKT41 in H13; auto.
      apply H8 in H11 as [f[H11[]]]. elim (@ MKT16 f).
      rewrite <-H13. apply AxiomII; split; auto.
      apply MKT75. destruct H11; auto. rewrite H14; auto. }
    apply H9,AxiomII in H12 as []; auto. }
  set (A1 := \{\ λ u v, u ∈ ω /\ v ∈ fA[u] \}\).
  assert ((ω × ω) ≈ A1).
  { set (h := \{\ λ u v, u ∈ (ω × ω)
      /\ v = [(First u),(g (First u))[Second u]] \}\).
    exists h. repeat split; unfold Relation; intros.
    - apply AxiomII in H12 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H12 as [_[]].
      apply AxiomII' in H13 as [_[]]. rewrite H14,H15; auto.
    - apply AxiomII in H12 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H12 as []. apply AxiomII' in H13 as [].
      apply AxiomII' in H14 as [H14[]].
      apply AxiomII' in H15 as [H15[]].
      apply AxiomII in H16 as [H16[y1[y2[H20[]]]]].
      apply AxiomII in H18 as [H18[z1[z2[H23[]]]]].
      assert (First y = y1 /\ First z = z1) as [].
      { rewrite H20,H23. split; apply MKT54a; eauto. }
      assert (Second y = y2 /\ Second z = z2) as [].
      { rewrite H20,H23. split; apply MKT54b; eauto. }
      rewrite H26,H28 in H17. rewrite H27,H29 in H19.
      assert (Ensemble x). { apply MKT49b in H12; tauto. }
      rewrite H17 in H19. rewrite H17 in H30.
      apply MKT49b in H30 as []. apply MKT55 in H19 as []; auto.
      rewrite H19 in H32. apply H11 in H24 as [[][]].
      apply f11inj in H32; auto; try rewrite H34; auto.
      rewrite H20,H23,H19,H32; auto.
    - apply AxiomI; split; intros. apply AxiomII in H12 as [_[]].
      apply AxiomII' in H12 as [_[]]; auto.
      apply AxiomII; split; eauto. pose proof H12.
      apply AxiomII in H13 as [H13[z1[z2[H14[]]]]].
      assert (First z = z1 /\ Second z = z2) as [].
      { rewrite H14; split; [rewrite MKT54a|rewrite MKT54b];
        eauto. }
      exists ([z1,(g z1)[z2]]). apply AxiomII'; rewrite H17,H18;
      split; auto. apply MKT49a; auto. apply MKT49a; eauto.
      apply H11 in H15 as [[][]]. rewrite <-H20 in H16.
      apply Property_Value,Property_ran in H16; eauto.
    - apply AxiomI; split; intros. apply AxiomII in H12 as [H12[]].
      apply AxiomII' in H13 as [H13[]].
      apply AxiomII in H14 as [H14[x1[x2[H16[]]]]].
      assert (First x = x1 /\ Second x = x2) as [].
      { rewrite H16; split; [rewrite MKT54a|rewrite MKT54b]; eauto. }
      rewrite H19,H20 in H15. pose proof H17.
      apply H11 in H21 as [[][]]. rewrite <-H23 in H18.
      apply Property_Value,Property_ran in H18; auto.
      rewrite H24 in H18. rewrite H15. apply AxiomII'; split; auto.
      apply MKT49a; eauto.
      apply AxiomII in H12 as [H12[z1[z2[H13[]]]]].
      pose proof H14. apply H11 in H16 as [[][]].
      rewrite <-H19 in H15. apply Einr in H15 as [x[]]; auto.
      apply AxiomII; split; auto. rewrite H18 in H15.
      exists [z1,x]. apply AxiomII'; split. apply MKT49a; auto.
      apply MKT49a; eauto. split. apply AxiomII'; split; auto.
      apply MKT49a; eauto.
      assert (First ([z1,x]) = z1 /\ Second ([z1,x]) = x) as [].
      { split; [rewrite MKT54a|rewrite MKT54b]; eauto. }
      rewrite H21,H22. rewrite <-H20; auto. }
  assert (Ensemble (ω × ω)). { apply MKT74; auto. }
  assert (Ensemble A1). { apply MKT146,eqvp in H12; auto. }
  apply MKT154 in H12; auto.
  assert (P[ω × ω] = ω).
  { apply MKT179. apply MKT4'; split. apply MKT165.
    apply AxiomII; split; auto. apply MKT101. }
  set (h := \{\ λ u v, u ∈ A1 /\ v = (Second u) \}\).
  assert (Function h /\ dom(h) = A1 /\ ran(h) = ∪A) as [H16[]].
  { repeat split; unfold Relation; intros.
    - apply AxiomII in H16 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H16 as [_[]].
      apply AxiomII' in H17 as [_[]]. rewrite H18,H19; auto.
    - apply AxiomI; split; intros. apply AxiomII in H16 as [_[]].
      apply AxiomII' in H16 as [_[]]; auto. pose proof H16.
      apply AxiomII in H17 as [H17[z1[z2[H18[]]]]].
      apply AxiomII; split; auto. exists z2.
      apply AxiomII'; split. apply MKT49a; eauto. split; auto.
      rewrite H18,MKT54b; eauto.
    - apply AxiomI; split; intros. apply AxiomII in H16 as [H16[]].
      apply AxiomII' in H17 as [H17[]]. apply AxiomII in H18
      as [H18[x1[x2[H20[]]]]]. apply AxiomII; split; auto.
      exists fA[x1]. split. rewrite H19,H20,MKT54b; eauto.
      rewrite <-H6 in H21. apply Property_Value,Property_ran
      in H21; auto. rewrite H7 in H21; auto.
      apply AxiomII in H16 as [H16[x[]]].
      apply AxiomII; split; auto. rewrite <-H7 in H18.
      apply Einr in H18 as [x0[]]; auto. rewrite H6 in H18.
      exists [x0,z]. apply AxiomII'; split. apply MKT49a; auto.
      apply MKT49a; eauto. split. apply AxiomII'; split.
      apply MKT49a; eauto. rewrite <-H19; auto.
      rewrite MKT54b; eauto. }
  assert (Ensemble h). { apply MKT75; auto. rewrite H17; auto. }
  pose proof H16. apply MKT160 in H20; auto.
  rewrite H17,H18,<-H12,H15 in H20. pose proof in_ω_0.
  rewrite <-H6 in H21. apply Property_Value,Property_ran in H21;
  auto. rewrite H7 in H21. pose proof H21. apply H0 in H21.
  assert (fA[Φ] ⊂ (∪A)).
  { unfold Included; intros. apply AxiomII; split; eauto. }
  apply MKT158 in H23. rewrite H21 in H23. destruct H20,H23; auto.
  elim (MKT102 P[∪A] ω); auto.
Qed.

Lemma Existence_of_NPAUF_Lemma15 : ∀ A B, P[A] = ω -> P[B] ≼ ω
  -> P[A ∪ B] = ω.
Proof.
  intros. destruct H0.
  - set (p := fun n => (∀ B0, P[B0] = n -> P[A ∪ B0] = ω)).
    assert (∀ n, n ∈ ω -> p n).
    { apply Mathematical_Induction; unfold p; intros.
      apply carE in H1. rewrite H1,MKT6,MKT17; auto. pose proof H3.
      apply Inf_P7_Lemma in H4 as [B1[b[J[H7[H4[]]]]]]; auto.
      destruct (classic (b ∈ A)).
      assert (A ∪ B0 = A ∪ B1).
      { apply AxiomI; split; intros. apply MKT4. apply MKT4 in H9
        as []; auto. rewrite H6 in H9. apply MKT4 in H9 as []; auto.
        apply MKT41 in H9; auto. rewrite H9; auto. apply MKT4.
        apply MKT4 in H9 as []; auto. right. rewrite H6.
        apply MKT4; auto. }
      rewrite H9. apply H2; auto. rewrite H6,<-MKT7.
      pose proof H4. apply H2 in H9.
      assert (Ensemble (A ∪ B1)).
      { apply MKT19. apply NNPP; intro. rewrite <-MKT152b in H10.
        apply MKT69a in H10. pose proof MKT138.
        rewrite <-H9,H10 in H11. elim MKT39; eauto. }
      pose proof MKT165. apply MKT156 in H11 as [].
      rewrite <-H12 in H9. symmetry in H9. apply MKT154 in H9; auto.
      destruct H9 as [f[[][]]].
      assert ((PlusOne ω) ≈ (A ∪ B1) ∪ [b]).
      { exists (f ∪ [[ω,b]]). split. split. apply fupf; auto.
        rewrite H14. apply MKT101. rewrite uiv,siv; auto.
        apply fupf; auto. rewrite <-reqdi,H15. intro.
        apply MKT4 in H16 as []; auto.
        split; apply AxiomI; split; intros.
        - apply AxiomII in H16 as [H16[x]]. apply MKT4 in H17 as [].
          apply Property_dom in H17. rewrite H14 in H17.
          apply MKT4; auto. pose proof H17. apply MKT41 in H18;
          auto. apply MKT55 in H18 as []; auto. apply MKT4; right.
          apply MKT41; auto. assert (Ensemble ([z,x])); eauto.
          apply MKT49b in H20; tauto.
        - apply AxiomII; split; eauto. apply MKT4 in H16 as [].
          rewrite <-H14 in H16. apply Property_Value in H16; auto.
          exists f[z]. apply MKT4; auto. pose proof H16.
          apply MKT41 in H17; auto. exists b. apply MKT4; right.
          rewrite H17. apply MKT41; auto.
        - apply AxiomII in H16 as [H16[x]]. apply MKT4 in H17 as [].
          apply Property_ran in H17. rewrite H15 in H17. apply MKT4;
          auto. apply MKT4; right. apply MKT41; auto.
          assert (Ensemble x). { apply Property_dom in H17; eauto. }
          apply MKT41 in H17; auto. apply MKT55 in H17; tauto.
        - apply AxiomII; split; eauto. apply MKT4 in H16 as [].
          rewrite <-H15 in H16. apply AxiomII in H16 as [H16[x]].
          exists x. apply MKT4; auto. apply MKT41 in H16; auto.
          exists ω. apply MKT4; right. rewrite H16.
          apply MKT41; auto. }
      apply MKT154 in H16; try apply AxiomIV; auto.
      assert (P[PlusOne ω] = P[ω]).
      { apply MKT174. apply MKT4'; split. apply MKT138.
        apply AxiomII; split; auto. apply MKT101. }
      rewrite <-H16,H17; auto. }
    apply H1 in H0; auto.
  - pose proof MKT165. apply MKT156 in H1 as [].
    assert (Ensemble A /\ Ensemble B) as [].
    { split; apply MKT19,NNPP; intro;
      rewrite <-MKT152b in H3; apply MKT69a in H3;
      elim MKT39; [rewrite <-H3,H|rewrite <-H3,H0]; auto. }
    assert (ω_E ≈ A /\ ω_O ≈ B) as [[f[[][]]][g[[][]]]].
    { split; apply (MKT147 ω). apply ω_E_Equivalent_ω.
      apply MKT154; auto. rewrite H2; auto. apply ω_O_Equivalent_ω.
      apply MKT154; auto. rewrite H2; auto. }
    assert (Function (f ∪ g) /\ dom(f ∪ g) = ω
      /\ ran(f ∪ g) = A ∪ B) as [H13[]].
    { rewrite <-ω_E_Union_ω_O,undom,H7,H11,unran,H8,H12.
      split; auto. split; unfold Relation; intros.
      apply MKT4 in H13 as []; rewrite MKT70 in H13; auto;
      apply AxiomII in H13 as [_[x[y[]]]]; eauto.
      apply MKT4 in H13 as [], H14 as []. destruct H5.
      apply (H15 x); auto. apply Property_dom in H13,H14.
      rewrite H7 in H13. rewrite H11 in H14. elim (@ MKT16 x).
      rewrite <-ω_E_Intersection_ω_O. apply MKT4'; auto.
      apply Property_dom in H13,H14. rewrite H7 in H14.
      rewrite H11 in H13. elim (@ MKT16 x).
      rewrite <-ω_E_Intersection_ω_O. apply MKT4'; auto.
      destruct H9. apply (H15 x); auto. }
    apply MKT160 in H13; [ |apply AxiomIV; apply MKT75; auto;
    [rewrite H7; apply ω_E_is_Set|rewrite H11; apply ω_O_is_Set]].
    rewrite H14,H15,H2 in H13.
    assert (A ⊂ (A ∪ B)).
    { unfold Included; intros. apply MKT4; auto. }
    apply MKT158 in H16. rewrite H in H16. destruct H13,H16; auto.
    elim (MKT102 ω P[A ∪ B]); auto.
Qed.

Lemma Existence_of_NPAUF_Lemma16 : ∀ A, P[A] = ω
  -> (∀ a, a ∈ A -> P[a] ≼ ω) -> P[∪A] ≼ ω.
Proof.
  intros. set (A1 := \{ λ u, ∃ a, a ∈ A /\ u = ω ∪ ([Φ] × a) \}).
  set (g := \{\ λ u v, u ∈ ((∪A1) ~ ω) /\ v = Second u \}\).
  assert (Function g /\ dom(g) = (∪A1) ~ ω /\ ran(g) = ∪A).
  { repeat split; unfold Relation; try (apply AxiomI; split);
    intros.
    - apply AxiomII in H1 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H1 as [_[]]. apply AxiomII' in H2 as [_[]].
      rewrite H3,H4; auto.
    - apply AxiomII in H1 as [_[]]. apply AxiomII' in H1; tauto.
    - apply AxiomII; split; eauto. pose proof H1.
      apply MKT4' in H2 as []. apply AxiomII in H2 as [_[y[]]].
      apply AxiomII in H4 as [H4[x[]]]. rewrite H6 in H2.
      apply MKT4 in H2 as []. apply AxiomII in H3 as [_].
      elim H3; auto. apply AxiomII in H2 as [H2[z1[z2[H7[]]]]].
      exists z2. apply AxiomII'; split. apply MKT49a; eauto.
      split; auto. rewrite H7,MKT54b; eauto.
    - apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2
      as [H2[]]. apply AxiomII; split; auto.
      apply MKT4' in H3 as []. apply AxiomII in H3 as [H3[x0[]]].
      apply AxiomII in H7 as [H7[x1[]]]. exists x1. split; auto.
      rewrite H9 in H6. apply MKT4 in H6 as [].
      apply AxiomII in H5 as []. elim H10; auto.
      apply AxiomII in H6 as [H6[x2[x3[H10[]]]]].
      rewrite H4,H10,MKT54b; eauto.
    - apply AxiomII in H1 as [H1[x[]]].
      assert ([Φ,z] ∈ ((∪A1) ~ ω)).
      { pose proof in_ω_0. apply MKT4'; split.
        apply AxiomII; split; eauto. exists (ω ∪ ([Φ] × x)).
        split. apply MKT4; right. apply AxiomII'; split; auto.
        apply AxiomII; split; eauto. pose proof MKT138.
        apply AxiomIV; eauto. apply MKT74; eauto.
        apply AxiomII; split; auto. intro.
        assert ([Φ] ∈ [Φ,z]). { apply AxiomII; split; auto. }
        assert (Ordinal Φ /\ Ordinal ([Φ,z])) as [].
        { apply AxiomII in H4 as [_[]].
          apply AxiomII in H5 as [_[]]; auto. }
        apply (@ MKT110 Φ) in H8 as [H8|[|]]; auto.
        apply AxiomII in H8 as [_[]]. apply MKT41 in H8; auto.
        assert (Φ ∈ [Φ]); auto. rewrite <-H8 in H9.
        apply MKT101 in H9; auto. apply MKT41 in H8; auto.
        assert (Φ ∈ [Φ|z]). { apply AxiomII; auto. }
        rewrite <-H8 in H9. apply MKT101 in H9; auto.
        apply MKT16 in H8; auto. rewrite <-H8 in H6.
        apply MKT16 in H6; auto. }
      apply AxiomII; split; eauto. exists [Φ,z].
      apply AxiomII'; repeat split; auto. rewrite MKT54b; auto. }
  destruct H1 as [H1[]]. assert (((∪A1) ~ ω) ⊂ (∪A1)).
  { unfold Included; intros. apply MKT4' in H4 as []; auto. }
  assert (∀ a, a ∈ A1 -> P[a] = ω).
  { intros. apply AxiomII in H5 as [H5[x[]]].
    rewrite H7. apply Existence_of_NPAUF_Lemma15.
    apply MKT156,MKT165. pose proof H6. apply H0 in H8 as [].
    left. apply MKT170; auto. apply finsin; auto.
    rewrite <-(@ MKT179 ω),lem179a,H8; eauto. apply MKT158.
    pose proof in_ω_1. apply MKT164,MKT156 in H9 as [].
    rewrite H10. unfold Included; intros.
    apply AxiomII in H11 as [H11[z1[z2[H12[]]]]]. rewrite H12 in *.
    apply AxiomII'; repeat split; auto. apply MKT41 in H13; auto.
    rewrite H13; auto. pose proof MKT165. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. apply MKT101. }
  assert (A ≈ A1).
  { set (f := \{\ λ u v, u ∈ A /\ v = ω ∪ ([Φ] × u) \}\).
    exists f. repeat split; unfold Relation;
    try (apply AxiomI; split); intros.
    - apply AxiomII in H6 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H6 as [_[]]. apply AxiomII' in H7 as [_[]].
      rewrite H8,H9; auto.
    - apply AxiomII in H6 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H6 as [_]. apply AxiomII' in H7 as [_].
      apply AxiomII' in H6 as [H6[]]. apply AxiomII' in H7 as [H7[]].
      assert (∀ u, Ensemble u -> (ω ∪ ([Φ] × u)) ~ ω = [Φ] × u).
      { intros. apply AxiomI; split; intros.
        apply MKT4' in H13 as []. apply MKT4 in H13 as []; auto.
        apply AxiomII in H14 as [_]. elim H14; auto.
        apply MKT4'; split. apply MKT4; auto.
        apply AxiomII; split; eauto. intro.
        apply AxiomII in H13 as [H13[x1[x2[H15[]]]]].
        assert (Ordinal Φ /\ Ordinal ([x1,x2])) as [].
        { rewrite <-H15. apply AxiomII in H14 as [_[]].
          pose proof in_ω_0. apply AxiomII in H19 as [_[]]; auto. }
        apply (@ MKT110 Φ) in H19 as [H19|[|]]; auto.
        apply AxiomII in H19 as [_[]]. apply MKT41 in H19; eauto.
        assert (x1 ∈ [x1]); eauto. rewrite <-H19 in H20.
        apply MKT16 in H20; auto. apply MKT41 in H19.
        assert (x1 ∈ [x1|x2]). { apply AxiomII; split; eauto. }
        rewrite <-H19 in H20. apply MKT16 in H20; auto.
        apply MKT46a; eauto. apply MKT16 in H19; auto.
        assert ([x1] ∈ [x1,x2]).
        { apply AxiomII; split; eauto. left.
          apply MKT41; eauto. }
        rewrite <-H19 in H20. apply MKT16 in H20; auto. }
      assert (Ensemble y /\ Ensemble z) as []. split; eauto.
      apply H12 in H13,H14.
      assert (∀ u, ran([Φ] × u) = u).
      { intros. apply AxiomI; split; intros.
        apply AxiomII in H15 as [H15[]]. apply AxiomII' in H16;
        tauto. apply AxiomII; split; eauto. exists Φ.
        apply AxiomII'; split; auto. apply MKT49a; eauto. }
      rewrite <-H11,H9,H13 in H14.
      rewrite <-(H15 y),<-H15,H14; auto.
    - apply AxiomII in H6 as [H6[]]. apply AxiomII' in H7; tauto.
    - apply AxiomII; split; eauto. exists (ω ∪ ([Φ] × z)).
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      pose proof MKT138. apply AxiomIV; eauto. apply MKT74; eauto.
    - apply AxiomII in H6 as [H6[]]. apply AxiomII' in H7
      as [H7[]]. apply AxiomII; split; eauto.
    - apply AxiomII in H6 as [H6[x[]]].
      apply AxiomII; split; auto. exists x.
      apply AxiomII'; split; auto. apply MKT49a; eauto.  }
  assert (Ensemble A).
  { apply MKT19. apply NNPP; intro. rewrite <-MKT152b in H7.
    apply MKT69a in H7. pose proof MKT138. rewrite <-H,H7 in H8.
    elim MKT39; eauto. }
  pose proof H6. apply MKT146,eqvp in H8; auto.
  pose proof H8. apply AxiomVI in H9.
  pose proof H4. apply MKT33 in H10; auto.
  pose proof H10. rewrite <-H2 in H11. apply MKT75 in H11; auto.
  pose proof H1. apply MKT160 in H12; auto.
  apply MKT154 in H6; auto. apply MKT158 in H4.
  rewrite H in H6. apply Existence_of_NPAUF_Lemma14 in H5; auto.
  rewrite H2,H3 in H12. rewrite H5 in H4.
  destruct H4,H12; unfold LessEqual.
  pose proof MKT138. apply AxiomII in H13 as [_[]].
  apply H14 in H4; auto. rewrite <-H12 in H4; auto.
  rewrite H4 in H12; auto. rewrite H12; auto.
Qed.

Lemma Existence_of_NPAUF_Lemma17 : ∀ A, Finite A -> A <> Φ
  -> (∀ a, a ∈ A -> P[a] = ω) -> P[∪A] = ω.
Proof.
  intros. set (p n := ∀ A0, P[A0] = n -> A0 <> Φ
    -> (∀ a, a ∈ A0 -> P[a] = ω) -> P[∪A0] = ω).
  assert (∀ n, n ∈ ω -> p n).
  { apply Mathematical_Induction; unfold p; intros.
    apply carE in H2. elim H3; auto.
    assert (Ensemble A0).
    { apply MKT19,NNPP; intro. rewrite <-MKT152b in H7.
      apply MKT69a in H7. apply MKT134 in H2.
      rewrite <-H4,H7 in H2. elim MKT39; eauto. }
    apply Inf_P7_Lemma in H4 as [B[b[J[H10[H4[]]]]]]; auto.
    destruct (classic (B = Φ)). rewrite H11,MKT17 in H9.
    pose proof H10. apply MKT44 in H12 as [_].
    assert (b ∈ A0). { rewrite H9. apply MKT41; auto. }
    rewrite H9,H12; auto. pose proof H10. apply MKT44 in H12 as [_].
    assert (∪A0 = (∪B) ∪ b). { rewrite H9,Lemma169,H12; auto. }
    assert (P[∪B] = ω).
    { apply H3; auto. intros. apply H6. rewrite H9.
      apply MKT4; auto. }
    assert (P[b] = ω).
    { apply H6. rewrite H9. apply MKT4; right. apply MKT41; auto. }
    rewrite H13. apply Existence_of_NPAUF_Lemma15; auto.
    right; auto. }
  apply H2 in H; auto.
Qed.

Lemma Existence_of_NPAUF_Lemma18 : ∀ A, P[A] ≼ ω
  -> (∀ a, a ∈ A -> P[a] ≼ ω) -> P[∪A] ≼ ω.
Proof.
  intros. destruct H; [ |apply Existence_of_NPAUF_Lemma16; auto].
  set (A1 := \{ λ u, u ∈ A /\ P[u] = ω \}).
  set (A2 := \{ λ u, u ∈ A /\ P[u] ∈ ω \}).
  assert (A = A1 ∪ A2).
  { apply AxiomI; split; intros. pose proof H1. apply MKT4.
    apply H0 in H1 as []. right. apply AxiomII; split; eauto.
    left. apply AxiomII; split; eauto. apply MKT4 in H1 as [];
    apply AxiomII in H1; tauto. }
  pose proof MKT138. apply AxiomII in H2 as [H2[_]].
  pose proof MKT165. apply MKT156 in H4 as [_].
  assert (A1 ⊂ A /\ A2 ⊂ A) as [].
  { rewrite H1; split; unfold Included; intros; apply MKT4; auto. }
  assert (P[A1] ∈ ω /\ P[A2] ∈ ω) as [].
  { apply MKT158 in H5 as [], H6 as []; try rewrite H5;
    try rewrite H6; split; auto; apply H3 in H; auto. }
  assert (∪A = (∪A1) ∪ (∪A2)). { rewrite <-Lemma169,H1; auto. }
  assert (P[∪A2] ∈ ω).
  { apply MKT169; auto. intros. apply AxiomII in H10; tauto. }
  destruct (classic (A1 = Φ)). rewrite H11,MKT24',MKT17 in H9.
  rewrite H9. left; auto.
  assert (P[∪A1] = ω).
  { apply Existence_of_NPAUF_Lemma17; auto. intros.
    apply AxiomII in H12; tauto. }
  rewrite H9. right. apply Existence_of_NPAUF_Lemma15; auto.
  left; auto.
Qed.

Lemma Existence_of_NPAUF_Lemma19 :
  P[\{ λ u, u ⊂ ω /\ Finite u \}] = ω.
Proof.
  set (A1 := \{ λ u, ∃ n, n ∈ ω /\ u = pow(n) \}).
  assert (\{ λ u, u ⊂ ω /\ Finite u \} = ∪A1).
  { pose proof MKT138. apply AxiomII in H as [H[_]].
    apply AxiomI; split; intros.
    - apply AxiomII in H1 as [H1[]]. apply AxiomII; split; auto.
      pose proof H1. apply MKT153 in H4 as [g[[][]]].
      pose proof H3. destruct (classic (z = Φ)). rewrite H9.
      exists pow([Φ]). split; auto. apply AxiomII; split; auto.
      apply AxiomII; split. apply MKT38a; auto. exists [Φ].
      split; auto. apply in_ω_1; auto. pose proof H8.
      apply (Existence_of_NPAUF_Lemma6 ω z) in H10 as [z1[]]; auto.
      pose proof H10. apply H2,MKT134 in H12.
      exists pow(PlusOne z1). split. apply AxiomII; split; auto.
      unfold Included; intros. apply MKT4.
      assert (Ordinal z0 /\ Ordinal z1) as [].
      { apply H2,AxiomII in H10 as [_[]], H13 as [_[]]; auto. }
      apply (@ MKT110 z0) in H15 as [H15|[|]]; auto. pose proof H13.
      apply H11 in H13. elim H13. apply AxiomII'; split.
      apply MKT49a; eauto. apply AxiomII'; split; auto.
      apply MKT49a; eauto. right. apply MKT41; eauto.
      apply AxiomII; split; eauto. apply MKT38a; eauto.
    - apply AxiomII in H1 as [H1[x[]]]. apply AxiomII in H3
      as [H3[n[]]]. apply AxiomII; split; auto. rewrite H5 in H2.
      apply AxiomII in H2 as []. split. apply H0 in H4.
      unfold Included; intros; auto. apply MKT158 in H6.
      pose proof H4. apply MKT164,MKT156 in H7 as [].
      rewrite H8 in H6. destruct H6. apply H0 in H4.
      apply H4; auto. rewrite <-H6 in H4; auto. }
  assert (∀ a, a ∈ A1 -> Finite a).
  { intros. apply AxiomII in H0 as [H0[x[]]]. rewrite H2.
    apply MKT171. pose proof H1. apply MKT164,MKT156 in H3 as [].
    rewrite <-H4 in H1; auto. }
  assert (ω ≈ A1).
  { set (g := \{\ λ u v, u ∈ ω /\ v = pow(u) \}\).
    exists g. repeat split; unfold Relation;
    try (apply AxiomI; split); intros.
    - apply AxiomII in H1 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H1 as [_[]]. apply AxiomII' in H2 as [_[]].
      rewrite H3,H4; auto.
    - apply AxiomII in H1 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H1 as [_]. apply AxiomII' in H2 as [_].
      apply AxiomII' in H1 as [_[]]. apply AxiomII' in H2 as [_[]].
      assert (y ∈ pow(y) /\ z ∈ pow(z)) as [].
      { split; apply AxiomII; split; eauto. }
      rewrite <-H3,H4 in H5. rewrite <-H4,H3 in H6.
      apply AxiomII in H5 as []. apply AxiomII in H6 as [].
      apply MKT27; auto.
    - apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2; tauto.
    - apply AxiomII; split; eauto. exists pow(z).
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      apply MKT38a; eauto.
    - apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2 as [H2[]].
      apply AxiomII; split; eauto.
    - apply AxiomII in H1 as [H1[x[]]]. apply AxiomII; split; auto.
      exists x. apply AxiomII'; split; auto. apply MKT49a; eauto. }
  pose proof MKT165. apply MKT156 in H2 as [].
  pose proof H1. apply MKT146,eqvp in H4; auto.
  apply MKT154 in H1; auto. rewrite H3 in H1. symmetry in H1.
  apply Existence_of_NPAUF_Lemma16 in H1;
  [ |intros; left; apply H0; auto]. rewrite <-H in H1.
  set (A2 := \{ λ u, ∃ n, n ∈ ω /\ u = [n] \}).
  assert (A2 ⊂ \{ λ u, u ⊂ ω /\ Finite u \}).
  { unfold Included; intros. apply AxiomII in H5 as [H5[x[]]].
    apply AxiomII; split; auto. rewrite H7. split.
    unfold Included; intros. apply MKT41 in H8; eauto.
    rewrite H8; auto. apply finsin; eauto. }
  assert (ω ≈ A2).
  { set (g := \{\ λ u v, u ∈ ω /\ v = [u] \}\).
    exists g. repeat split; unfold Relation;
    try (apply AxiomI; split); intros.
    - apply AxiomII in H6 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H6 as [_[]]. apply AxiomII' in H7 as [_[]].
      rewrite H8,H9; auto.
    - apply AxiomII in H6 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H6 as [_]. apply AxiomII' in H7 as [_].
      apply AxiomII' in H6 as [_[]]. apply AxiomII' in H7 as [_[]].
      assert (Ensemble y /\ Ensemble z) as []. split; eauto.
      apply MKT44 in H10 as [H10 _]. apply MKT44 in H11 as [H11 _].
      rewrite <-H10,<-H11,<-H8,<-H9; auto.
    - apply AxiomII in H6 as [H6[]]. apply AxiomII' in H7; tauto.
    - apply AxiomII; split; eauto. exists [z].
      apply AxiomII'; split; auto. apply MKT49a; eauto.
    - apply AxiomII in H6 as [H6[]].
      apply AxiomII' in H7 as [H7[]]. apply AxiomII; split; eauto.
    - apply AxiomII in H6 as [H6[x[]]]. apply AxiomII; split; auto.
      exists x. apply AxiomII'; split; auto. apply MKT49a; eauto. }
  pose proof H6. apply MKT146,eqvp in H7; auto.
  apply MKT154 in H6; auto. apply MKT158 in H5.
  rewrite <-H6,H3 in H5. destruct H1,H5; auto.
  rewrite H in *. elim (MKT102 P[∪A1] ω); auto.
Qed.

Lemma Existence_of_NPAUF_Lemma20 : ∀ A, P[A] = ω
  -> P[\{ λ u, u ⊂ A /\ Finite u \}] = ω.
Proof.
  intros. pose proof MKT165. apply MKT156 in H0 as [].
  assert (Ensemble A).
  { apply MKT19,NNPP; intro. rewrite <-MKT152b in H2.
    apply MKT69a in H2. rewrite <-H,H2 in H0. elim MKT39; auto. }
  pose proof H. rewrite <-H1 in H3. symmetry in H3.
  apply MKT154 in H3 as [f[[][]]]; auto.
  set (A1 := \{ λ u, u ⊂ ω /\ Finite u \}).
  set (A2 := \{ λ u, u ⊂ A /\ Finite u \}).
  set (g := \{\ λ u v, u ∈ A1 /\ v = f「u」 \}\).
  assert (Function1_1 g /\ dom(g) = A1 /\ ran(g) = A2) as [H7[]].
  { repeat split; unfold Relation;
    try (apply AxiomI; split); intros.
    - apply AxiomII in H7 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H7 as [_[]]. apply AxiomII' in H8 as [_[]].
      rewrite H9,H10; auto.
    - apply AxiomII in H7 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H7 as [_]. apply AxiomII' in H8 as [_].
      apply AxiomII' in H7 as [_[]]. apply AxiomII' in H8 as [_[]].
      assert (f⁻¹「f「y」」 = f⁻¹「f「z」」).
      { rewrite <-H9,<-H10; auto. }
      apply AxiomII in H7 as [_[H7 _]], H8 as [_[H8 _]].
      rewrite <-(ImageSet_Property7 f y),<-(ImageSet_Property7 f z)
      in H11; try rewrite H5; try split; auto.
    - apply AxiomII in H7 as [_[]]. apply AxiomII' in H7; tauto.
    - apply AxiomII; split; eauto. exists f「z」.
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      apply (MKT33 A); auto. unfold Included; intros.
      apply AxiomII in H8 as [_[x[]]]. apply AxiomII in H7 as [_[]].
      apply H7 in H9. rewrite <-H5 in H9.
      apply Property_Value,Property_ran in H9; auto.
      rewrite <-H6,H8; auto.
    - apply AxiomII in H7 as [H7[]]. apply AxiomII' in H8 as [H8[]].
      apply AxiomII in H9 as [H9[]].
      assert (z ⊂ A).
      { unfold Included; intros. rewrite H10 in H13.
        apply AxiomII in H13 as [H13[x0[]]]. apply H11 in H15.
        rewrite <-H5 in H15. apply Property_Value,Property_ran
        in H15; auto. rewrite <-H14 in H15. rewrite <-H6; auto. }
      assert (x ≈ z).
      { exists (f|(x)). split. split. apply MKT126a; auto.
        split; unfold Relation; intros.
        apply AxiomII in H14 as [_[u[v[]]]]; eauto.
        apply AxiomII' in H14 as [], H15 as [].
        apply MKT4' in H16 as [H16 _], H17 as [H17 _].
        destruct H4. apply (H18 x0); auto; apply AxiomII'; auto.
        assert (dom(f|(x)) = x).
        { rewrite MKT126b; auto. rewrite H5.
          apply MKT30 in H11; auto. }
        split; auto. apply AxiomI; split; intros. pose proof H15.
        apply Einr in H16 as [x0[]]. rewrite H10.
        apply AxiomII; split; eauto. exists x0. rewrite <-H14.
        split; auto. rewrite MKT126c in H17; auto.
        apply MKT126a; auto. rewrite H10 in H15.
        apply AxiomII in H15 as [H15[x0[]]]. pose proof H17.
        rewrite <-H14 in H18. apply Property_Value,Property_ran
        in H18. rewrite MKT126c in H18; auto. rewrite H16; auto.
        rewrite H14; auto. apply MKT126a; auto. }
      pose proof H14. apply MKT146,eqvp in H14; auto.
      apply MKT154 in H15; auto. apply AxiomII; repeat split; auto.
      unfold Finite. rewrite <-H15; auto.
    - apply AxiomII in H7 as [H7[]]. apply AxiomII; split; auto.
      assert (f⁻¹「z」 ⊂ ω).
      { unfold Included; intros. apply AxiomII in H10 as [_[]].
        rewrite H5 in H10; auto. }
      assert (Ensemble (f⁻¹「z」)). { apply (MKT33 ω); auto. }
      exists f⁻¹「z」. apply AxiomII'; split. apply MKT49a; auto.
      split; [ |rewrite ImageSet_Property8_b; auto;
      rewrite H6; auto]. apply AxiomII; repeat split; auto.
      assert (z ≈ f⁻¹「z」).
      { exists (f⁻¹|(z)). pose proof H4. apply (MKT126a _ z) in H12.
        split. split; auto. split; unfold Relation; intros.
        apply AxiomII in H13 as [_[u[v[]]]]; eauto.
        apply AxiomII' in H13 as [_], H14 as [_].
        apply MKT4' in H13 as [H13 _], H14 as [H14 _].
        apply AxiomII' in H13 as [_], H14 as [_].
        destruct H3. apply (H15 x); auto.
        assert (dom(f⁻¹|(z)) = z).
        { rewrite MKT126b; auto. rewrite <-reqdi,H6.
          apply MKT30 in H8; auto. } split; auto.
        apply AxiomI; split; intros. apply AxiomII; split; eauto.
        apply Einr in H14 as [x[]]; auto. rewrite MKT126c in H15;
        auto. rewrite MKT126b in H14; auto. apply MKT4' in H14
        as []. split. rewrite H15. rewrite deqri.
        apply (@ Property_ran x),Property_Value; auto.
        rewrite H15,f11vi; auto. rewrite reqdi; auto.
        apply AxiomII in H14 as [H14[]]. apply AxiomII; split; auto.
        exists f[z0]. apply MKT4'; split; [ |apply AxiomII'; split;
        [apply MKT49a; eauto|split; auto]]. apply AxiomII'; split.
        apply MKT49a; eauto. apply Property_Value in H15; auto. }
      apply MKT154 in H12; auto. unfold Finite.
      rewrite <-H12; auto. }
  assert (A1 ≈ A2). { exists g; auto. }
  assert (Ensemble A1).
  { apply (MKT33 pow(ω)). apply MKT38a; auto.
    unfold Included; intros. apply AxiomII in H11 as [H11[]].
    apply AxiomII; auto. }
  pose proof H10. apply MKT146,eqvp in H12; auto.
  apply MKT154 in H10; auto. rewrite <-H10.
  apply Existence_of_NPAUF_Lemma19.
Qed.

Lemma Existence_of_NPAUF_Lemma21 : P[Fσ] = ω.
Proof.
  set (A := \{ λ u, u ⊂ ω /\ Finite u \}).
  set (f := \{\ λ u v, u ∈ A /\ v = ω ~ u \}\).
  assert (A ≈ Fσ).
  { exists f. repeat split; unfold Relation;
    try (apply AxiomI; split); intros.
    - apply AxiomII in H as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H as [_[]]. apply AxiomII' in H0 as [_[]].
      rewrite H1,H2; auto.
    - apply AxiomII in H as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H as [_]. apply AxiomII' in H0 as [_].
      apply AxiomII' in H as [_[]]. apply AxiomII' in H0 as [_[]].
      apply AxiomII in H as [H[]]. apply AxiomII in H0 as [H0[]].
      assert (y = ω ~ x).
      { apply AxiomI; split; intros. apply MKT4'; split; auto.
        apply AxiomII; split; eauto. intro. rewrite H1 in H8.
        apply MKT4' in H8 as [_]. apply AxiomII in H8 as []; auto.
        apply NNPP; intro. apply MKT4' in H7 as [].
        apply AxiomII in H9 as []. elim H10. rewrite H1.
        apply MKT4'; split; auto. apply AxiomII; auto. }
      assert (z = ω ~ x).
      { apply AxiomI; split; intros. apply MKT4'; split; auto.
        apply AxiomII; split; eauto. intro. rewrite H2 in H9.
        apply MKT4' in H9 as [_]. apply AxiomII in H9 as []; auto.
        apply NNPP; intro. apply MKT4' in H8 as [].
        apply AxiomII in H10 as []. elim H11. rewrite H2.
        apply MKT4'; split; auto. apply AxiomII; auto. }
      rewrite H7,H8; auto.
    - apply AxiomII in H as [H[y]]. apply AxiomII' in H0; tauto.
    - apply AxiomII; split; eauto. exists (ω ~ z).
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      apply (MKT33 ω). pose proof MKT138; eauto.
      unfold Included; intros. apply MKT4' in H0; tauto.
    - apply AxiomII in H as [H[]]. apply AxiomII' in H0 as [H0[]].
      apply AxiomII in H1 as [H1[]]. apply AxiomII; split; auto.
      split. rewrite H2. unfold Included; intros.
      apply MKT4' in H5; tauto. rewrite H2.
      replace (ω ~ (ω ~ x)) with x; auto.
      apply AxiomI; split; intros. apply MKT4'; split; auto.
      apply AxiomII; split; eauto. intro. apply MKT4' in H6 as [].
      apply AxiomII in H7 as []; auto. apply MKT4' in H5 as [].
      apply AxiomII in H6 as []. apply NNPP; intro. elim H7.
      apply MKT4'; split; auto. apply AxiomII; auto.
    - apply AxiomII in H as [H[]]. apply AxiomII; split; auto.
      exists (ω ~ z). pose proof H1. apply Property_Finite in H2.
      apply AxiomII'; split. apply MKT49a; auto. split.
      apply AxiomII; repeat split; auto. unfold Included; intros.
      apply MKT4' in H3; tauto. apply AxiomI; split; intros.
      apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT4' in H4 as []. apply AxiomII in H5 as [];
      auto. apply MKT4' in H3 as []. apply AxiomII in H4 as [].
      apply NNPP; intro. elim H5. apply MKT4'; split; auto.
      apply AxiomII; auto. }
  destruct (Fσ_is_just_Filter ω) as [H0 _]. unfold Finite. rewrite Inf_P1.
  apply MKT101. New MKT138; eauto. pose proof H.
  apply MKT154 in H; eauto with Fi. rewrite <-H.
  apply Existence_of_NPAUF_Lemma19. apply eqvp in H; eauto with Fi.
Qed.

Lemma Existence_of_NPAUF_Lemma22 : ∀ G, P[G] = ω -> P[〈G〉→ᵇ] = ω.
Proof.
  intros. pose proof MKT165. apply MKT156 in H0 as [].
  assert (Ensemble G).
  { apply MKT19,NNPP; intro. rewrite <-MKT152b in H2.
    apply MKT69a in H2. elim MKT39. rewrite <-H2,H; auto. }
  set (B n := \{ λ u, ∃ A, A ⊂ G /\ P[A] = n /\ u = ∩A \}).
  assert (B Φ = Φ).
  { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
    apply AxiomII in H3 as [H3[x[H4[]]]]. apply carE in H5.
    rewrite H6,H5,MKT24 in H3. elim MKT39; auto. }
  set (A n := \{ λ u, u ⊂ G /\ P[u] = n \}).
  set (f n := \{\ λ u v, u ∈ (A n) /\ v = ∩u\}\).
  assert (∀ n, n ∈ (ω ~ [Φ]) -> Function (f n) /\ dom(f n) = A n
    /\ ran(f n) = B n).
  { intros. repeat split; unfold Relation;
    try (apply AxiomI; split); intros.
    - apply AxiomII in H5 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H5 as [_[]]. apply AxiomII' in H6 as [_[]].
      rewrite H7,H8; auto.
    - apply AxiomII in H5 as [_[]]. apply AxiomII' in H5; tauto.
    - pose proof H5. apply AxiomII in H6 as [H6[]].
      apply AxiomII; split; auto. exists (∩z).
      apply AxiomII'; split; auto. apply MKT49a; auto.
      assert (z <> Φ).
      { intro. rewrite H9 in H8. pose proof in_ω_0.
        apply MKT164,MKT156 in H10 as [].
        apply MKT4' in H4 as [_]. apply AxiomII in H4 as [].
        elim H12. rewrite <-H8,H11; auto. }
      apply NEexE in H9 as [z0]. apply (MKT33 z0); eauto.
      unfold Included; intros. apply AxiomII in H10 as []; auto.
    - apply AxiomII in H5 as [H5[]].
      apply AxiomII' in H6 as [H6[]]. apply AxiomII; split; auto.
      apply AxiomII in H7 as [H7[]]. eauto.
    - pose proof H5. apply AxiomII in H6 as [H6[x[H7[]]]].
      apply AxiomII; split; auto. exists x.
      assert (Ensemble x).
      { apply MKT19,NNPP; intro. rewrite <-MKT152b in H10.
        apply MKT69a in H10. rewrite <-H8,H10 in H4.
        elim MKT39; eauto. }
      apply AxiomII'; repeat split; auto. apply AxiomII; auto. }
  assert (∀ n, n ∈ ω -> Ensemble (A n) /\ P[A n] ≼ ω).
  { intros. assert ((A n) ⊂ \{ λ u, u ⊂ G /\ Finite u \}).
    { unfold Included; intros. apply AxiomII in H6 as [H6[]].
      apply AxiomII; repeat split; auto. rewrite <-H8 in H5; auto. }
    split. apply (MKT33 pow(G)). apply MKT38a; auto.
    unfold Included; intros. apply AxiomII in H7 as [H7[]].
    apply AxiomII; auto. apply MKT158 in H6.
    rewrite Existence_of_NPAUF_Lemma20 in H6; auto. }
  assert (∀ n, n ∈ ω -> Ensemble (B n) /\ P[B n] ≼ ω).
  { intros. destruct (classic (n = Φ)).
    rewrite H7,H3. split; auto. rewrite H7 in H6.
    apply MKT164,MKT156 in H6 as []. rewrite H8. left; auto.
    assert (n ∈ (ω ~ [Φ])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H8; auto. }
    apply H4 in H8 as [H8[]]. apply MKT160 in H8;
    [ |apply MKT75; auto; rewrite H9; apply H5]; auto.
    rewrite H9,H10 in H8. apply H5 in H6 as [].
    split. apply MKT19,NNPP; intro. rewrite <-MKT152b in H12.
    apply MKT69a in H12. rewrite H12 in H8. elim MKT39.
    destruct H8; [ |rewrite H8]; eauto. destruct H11,H8;
    try rewrite <-H11; try rewrite H8; unfold LessEqual; auto.
    pose proof MKT138. apply AxiomII in H12 as [_[]].
    apply H13 in H11; auto. }
  set (D := \{ λ u, ∃ n, n ∈ ω /\ u = B n \}).
  assert (〈G〉→ᵇ = ∪D).
  { apply AxiomI; split; intros.
    - apply AxiomII in H7 as [H7[x[H8[]]]]. apply AxiomII; split;
      auto. exists (B P[x]). split. apply AxiomII; split; eauto.
      apply AxiomII; split; eauto. apply H6; auto.
    - apply AxiomII in H7 as [H7[x[]]].
      apply AxiomII in H9 as [H9[x0[]]]. rewrite H11 in H8.
      apply AxiomII in H8 as [_[x1[H8[]]]]. rewrite <-H12 in H10.
      apply AxiomII; split; eauto. }
  assert (∀ a, a ∈ D -> P[a] ≼ ω).
  { intros. apply AxiomII in H8 as [H8[x[]]].
    rewrite H10. apply H6; auto. }
  set (g := \{\ λ u v, u ∈ ω /\ v = B u \}\).
  assert (Function g /\ dom(g) = ω /\ ran(g) = D) as [H9[]].
  { repeat split; unfold Relation;
    try (apply AxiomI; split); intros.
    - apply AxiomII in H9 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H9 as [_[_]].
      apply AxiomII' in H10 as [_[_]]. rewrite H9,H10; auto.
    - apply AxiomII in H9 as [_[]]. apply AxiomII' in H9; tauto.
    - apply AxiomII; split; eauto. exists (B z).
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      apply H6; auto.
    - apply AxiomII in H9 as [H9[]]. apply AxiomII' in H10 as [_[]].
      apply AxiomII; split; eauto.
    - apply AxiomII in H9 as [H9[x[]]]. apply AxiomII; split; auto.
      exists x. apply AxiomII'; split; auto. apply MKT49a; eauto. }
  apply MKT160 in H9; [ |apply MKT75; auto; rewrite H10; auto].
  rewrite H10,H11,H1 in H9.
  apply Existence_of_NPAUF_Lemma18 in H9; auto. rewrite <-H7 in H9.
  pose proof (FilterBase_from_Fact G). apply MKT158 in H12. rewrite H in H12.
  destruct H9,H12; auto. elim (MKT102 P[〈G〉→ᵇ] ω); auto.
Qed.

(* The Continuum Hypothesis (CH ): there are non cardinal numbers
   between ω and P[pow(ω)] *)
Axiom CH : ∀ c, c ∈ C -> ω ≺ c -> P[pow(ω)] ≼ c.

(* with CH, there exists a non-principal arithmetical ultrafilter *)
Theorem Existence_of_NPAUF : ∃ F0, Arithmetical_ultraFilter F0 ω
  /\ (∀ n, F0 <> F n).
Proof.
  assert (Ensemble ω). { pose proof MKT165. eauto. }
  assert (Ensemble (pow(ω))). { apply MKT38a; auto. }
  pose proof Existence_of_NPAUF_Lemma11.
  assert (pow(ω) ≈ P[pow(ω)]). { apply MKT146,MKT153; auto. }
  apply (MKT147 _ _ P[pow(ω)]),MKT146 in H1; auto. clear H2.
  assert (P[pow(ω)] ∈ C). { apply Property_PClass; auto. }
  pose proof H2. apply AxiomII in H3 as [_[H3 _]].
  apply AxiomII in H3 as [_]. destruct H1 as [φ[[][]]].
  assert ((∀ n, n ∈ P[pow(ω)] -> Function (First φ[n])
    /\ dom(First φ[n]) = ω /\ ran(First φ[n]) ⊂ ω)
    /\ (∀ n, n ∈ P[pow(ω)] -> Function (Second φ[n])
    /\ dom(Second φ[n]) = ω /\ ran(Second φ[n]) ⊂ ω)) as [].
  { split; intros; rewrite <-H5 in H7; apply Property_Value,
    Property_ran in H7; auto; rewrite H6 in H7;
    apply AxiomII in H7 as [H7[x[y[H8[]]]]]; rewrite H8;
    apply AxiomII in H9 as []; apply AxiomII in H10 as [];
    [rewrite MKT54a|rewrite MKT54b]; auto. }
  set (e := \{\ λ α v, α ∈ P[pow(ω)] /\ v = \{ λ n, n ∈ ω
    /\ (First φ[α])[n] = (Second φ[α])[n] \} \}\).
  assert (Function e /\ dom(e) = P[pow(ω)]) as [H9a H9b].
  { repeat split; unfold Relation; intros. apply AxiomII in H9
    as [_[x[y[]]]]; eauto. apply AxiomII' in H9 as [_[]].
    apply AxiomII' in H10 as [_[]]. rewrite H11,H12; auto.
    apply AxiomI; split; intros. apply AxiomII  in H9 as [_[]].
    apply AxiomII' in H9; tauto. apply AxiomII; split; eauto.
    exists (\{ λ m, m ∈ ω /\ (First φ[z])[m] = (Second φ[z])[m] \}).
    apply AxiomII'; split; auto. apply MKT49a; eauto.
    apply (MKT33 ω); auto. unfold Included; intros.
    apply AxiomII in H10; tauto. }
  assert (∀ α, α ∈ P[pow(ω)] -> e[α] = \{ λ m, m ∈ ω
    /\ (First φ[α])[m] = (Second φ[α])[m] \}).
  { intros. rewrite <-H9b in H9. apply Property_Value,AxiomII'
    in H9 as [_[]]; auto. }
  destruct AxiomIX as [c[]].
  set (h := \{\ λ u v, Ordinal dom(u) /\
    ((dom(u) = Φ /\ v = Fσ)
  \/ (dom(u) <> Φ /\
       ((∃ m, LastMember m E dom(u) /\
            ((Finite_Intersection (u[m] ∪ [e[m]]) /\ v = 〈(u[m] ∪ [e[m]])〉→ᵇ)
          \/ (~ Finite_Intersection (u[m] ∪ [e[m]]) /\
                 ((∃ b, Finite b /\ b ⊂ ω /\ ((First φ[m])⁻¹「(Second φ[m])「b」」
                     ∪ (Second φ[m])⁻¹「(First φ[m])「b」」) ∈ 〈u[m]〉→ᶠ /\ v = u[m])
               \/ ((∀ b, Finite b -> b ⊂ ω -> ((First φ[m])⁻¹「(Second φ[m])「b」」
                     ∪ (Second φ[m])⁻¹「(First φ[m])「b」」) ∉ 〈u[m]〉→ᶠ) /\
                  v = 〈u[m] ∪ [c[\{ λ w, w ⊂ ω /\ Finite_Intersection (u[m] ∪ [w])
                      /\ (First φ[m])「w」 ∩ (Second φ[m])「w」 = Φ\}]]〉→ᵇ)))))
     \/ (~ (∃ m, LastMember m E dom(u)) /\ v = ∪(ran(u)))))) \}\).
  assert (Function h).
  { split; unfold Relation; intros. apply AxiomII in H12
    as [_[x[y[]]]]. eauto. apply AxiomII' in H12 as [_[]].
    apply AxiomII' in H13 as [_[]]. destruct H14,H15;
    destruct H14,H15. rewrite H16,H17; auto. elim H15; auto.
    elim H14; auto. clear H14 H15. destruct H16,H17.
    destruct H14 as [m1[]]. destruct H15 as [m2[]].
    assert (m1 = m2).
    { clear H16 H17. destruct H14,H15.
      assert (Ordinal m1 /\ Ordinal m2) as [].
      { split; [apply MKT111 in H14|apply MKT111 in H15]; auto. }
      apply (@ MKT110 m1 m2) in H19 as [H19|[|]]; auto.
      pose proof H15. apply H16 in H20. elim H20.
      apply AxiomII'; split. apply MKT49a; eauto.
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      pose proof H14. apply H17 in H20. elim H20.
      apply AxiomII'; split. apply MKT49a; eauto.
      apply AxiomII'; split; auto. apply MKT49a; eauto. }
    destruct H16,H17; destruct H16,H17. rewrite H19,H20,H18; auto.
    elim H17. rewrite <-H18; auto. elim H16. rewrite H18; auto.
    destruct H19,H20. destruct H19 as [b1[H19[H21[]]]].
    destruct H20 as [b2[H20[H24[]]]]. rewrite H23,H26,H18; auto.
    destruct H19 as [b[H19[H21[]]]]. destruct H20.
    apply H20 in H19; auto. elim H19. rewrite <-H18; auto.
    destruct H20 as [b[H20[H21[]]]]. destruct H19.
    apply H19 in H20; auto. elim H20. rewrite H18; auto.
    destruct H19,H20. rewrite H21,H22,H18; reflexivity.
    destruct H14 as [m[]]. destruct H15. elim H15; eauto.
    destruct H15 as [m[]]. destruct H14. elim H14; eauto.
    destruct H14,H15. rewrite H16,H17; auto. }
  destruct (MKT128a h) as [r[H13[]]].
  assert (∀ x, x ∈ R -> Ensemble (r|(x))).
  { intros. apply MKT75. apply MKT126a; auto. rewrite MKT126b;
    auto. apply (MKT33 x); eauto. unfold Included; intros.
    apply AxiomII in H17; tauto. }
  assert (r[Φ] = Fσ).
  { pose proof in_ω_0. apply AxiomII in H17 as [H17[H18 _]].
    assert (dom(r|(Φ)) = Φ). { rewrite MKT126b,MKT17'; auto. }
    assert ([r|(Φ),Fσ] ∈ h).
    { apply AxiomII'. rewrite H19. split; auto. apply MKT49a.
      apply H16,AxiomII; auto. destruct (Fσ_is_just_Filter ω); eauto with Fi.
      unfold Finite. rewrite Inf_P1. apply MKT101. }
    apply Property_Fun in H20; auto. rewrite H15; auto.
    apply AxiomII; auto. }
  assert (∀ m n, m ∈ n -> r[m] ⊂ r[n]).
  { intros. destruct (classic (m ∈ dom(r))).
    destruct (classic (n ∈ dom(r))). apply NNPP; intro.
    set (A := \{ λ u, u ∈ dom(r)
      /\ (∃ v, v ∈ u /\ ~ r[v] ⊂ r[u]) \}).
    assert (A ⊂ R /\ A <> Φ) as [].
    { split. unfold Included; intros. apply AxiomII in H22
      as [H22[]]. apply MKT111 in H23; auto. apply AxiomII; auto.
      apply NEexE. exists n. apply AxiomII; split; eauto. }
    assert (WellOrdered E R).
    { pose proof MKT113a. apply MKT107 in H24; auto. }
    destruct H24. apply H25 in H22 as []; auto. clear H23 H24 H25.
    destruct H22. apply AxiomII in H22 as [_[H22[x0[]]]].
    assert (∀ u v, u ∈ x -> v ∈ x -> u ∈ v -> r[u] ⊂ r[v]).
    { intros. apply NNPP; intro. assert (v ∈ A).
      { apply AxiomII; repeat split; eauto.
        destruct H14. apply H30 in H22; auto. }
      apply H23 in H30. elim H30. apply AxiomII'; split; auto.
      apply MKT49a; eauto. }
    destruct (classic (x = Φ)). rewrite H27 in H24.
    elim (@ MKT16 x0); auto.
    assert (x ∈ R).
    { apply AxiomII; split; eauto. apply MKT111 in H22; auto. }
    apply H15 in H28. assert (r|(x) ∈ dom(h)).
    { apply NNPP; intro. apply MKT69a in H29. apply MKT69b in H22.
      rewrite H28,H29 in H22. elim MKT39; eauto. }
    assert (dom(r|(x)) = x).
    { rewrite MKT126b; auto. destruct H14.
      apply H30,MKT30 in H22; auto. }
    apply Property_Value,AxiomII' in H29 as [H29[H31[]]]; auto.
    destruct H32. rewrite H30 in H32; auto. destruct H32 as [H32[]].
    destruct H33 as [x1[]]. assert ((r|(x))[x1] = r[x1]).
    { apply MKT126c; auto. destruct H33; auto. }
    assert (r[x1] ⊂ r[x]).
    { destruct H34. destruct H34. rewrite H36,H35 in H28.
      assert ((r[x1] ∪ [e[x1]]) ⊂ r[x]).
      { rewrite H28. apply FilterBase_from_Fact. }
      unfold Included; intros. apply H37. apply MKT4; auto.
      destruct H34 as [H34[]]. destruct H36 as [b[H36[_[]]]].
      rewrite H38,H35 in H28. rewrite H28; auto.
      destruct H36. rewrite H37,H35 in H28.
      assert ((r[x1] ∪ [c[\{ λ w, w ⊂ ω
        /\ Finite_Intersection (r[x1] ∪ [w])
        /\ (First φ[x1])「w」 ∩ (Second φ[x1])「w」 = Φ \}]]) ⊂ r[x]).
      { rewrite H28. apply FilterBase_from_Fact. }
      unfold Included; intros. apply H38. apply MKT4; auto. }
    elim H25. rewrite H30 in H33. pose proof H33.
    apply MKT133 in H37. pose proof H24. rewrite H37 in H38.
    apply MKT4 in H38 as []. apply H26 in H38; auto.
    unfold Included; intros. apply H38 in H39; auto.
    destruct H33; auto. apply MKT41 in H38. rewrite H38; auto.
    destruct H33; eauto. pose proof H22. apply MKT111 in H38; auto.
    apply AxiomII; split; eauto. destruct H33.
    pose proof H24. rewrite <-H30 in H35.
    pose proof H35. apply Property_Value,Property_ran in H36.
    elim H25. unfold Included; intros. rewrite H28,H34.
    apply AxiomII; split; eauto. exists (r[x0]). split; auto.
    rewrite MKT126c in H36; auto. apply MKT126a; auto.
    apply MKT69a in H20. rewrite H20. unfold Included; intros.
    apply MKT19; eauto. apply MKT69a in H19.
    destruct (classic (n ∈ dom(r))).
    assert (m ∈ dom(r)). { destruct H14. apply H21 in H20; auto. }
    apply MKT69b in H21. rewrite H19 in H21. elim MKT39; eauto.
    apply MKT69a in H20. rewrite H19,H20; auto. }
  assert (∀ n, n ∈ dom(r) -> FilterBase r[n] ω).
  { intros. apply NNPP; intro.
    set (A := \{ λ u, u ∈ dom(r) /\ ~ FilterBase r[u] ω \}).
    assert (A ⊂ R /\ A <> Φ) as [].
    { split. unfold Included; intros. apply AxiomII in H21
      as [H21[]]. apply MKT111 in H22; auto. apply AxiomII; auto.
      apply NEexE. exists n. apply AxiomII; split; eauto. }
    assert (WellOrdered E R).
    { pose proof MKT113a. apply MKT107 in H23; auto. }
    destruct H23. apply H24 in H21 as []; auto. clear H22 H23 H24.
    destruct H21. apply AxiomII in H21 as [_[]].
    assert (∀ u, u ∈ x -> FilterBase r[u] ω).
    { intros. apply NNPP; intro. assert (u ∈ A).
      { apply AxiomII; repeat split; eauto.
        destruct H14. apply H26 in H21; auto. }
      apply H22 in H26. elim H26. apply AxiomII'; split; auto.
      apply MKT49a; eauto. }
    destruct (classic (x = Φ)). rewrite H25,H17 in H23.
    elim H23. destruct (Fσ_is_just_Filter ω) as [[H26[H27[H28[]]]]]; eauto.
    unfold Finite. rewrite Inf_P1. apply MKT101. repeat split; auto.
    apply NEexE; eauto. assert (x ∈ R).
    { apply AxiomII; split; eauto. apply MKT111 in H21; auto. }
    pose proof H26. apply H15 in H27. assert (r|(x) ∈ dom(h)).
    { apply NNPP; intro. apply MKT69a in H28. apply MKT69b in H21.
      rewrite H27,H28 in H21. elim MKT39; eauto. }
    assert (dom(r|(x)) = x).
    { rewrite MKT126b; auto. destruct H14.
      apply H29,MKT30 in H21; auto. }
    apply Property_Value,AxiomII' in H28 as [H28[H30[]]]; auto.
    destruct H31. rewrite H29 in H31; auto. destruct H31 as [H31[]].
    destruct H32 as [x1[]]. assert ((r|(x))[x1] = r[x1]).
    { apply MKT126c; auto. destruct H32; auto. }
    rewrite H34,<-H27 in H33. rewrite H29 in H32.
    destruct H33; destruct H33. assert (x1 ∈ dom(e)).
    { apply NNPP; intro. apply MKT69a in H36. pose proof MKT39.
      apply MKT43 in H37. rewrite H36,H37,MKT20 in H33.
      assert ([Φ] ∩ [[Φ]] ⊂ μ).
      { unfold Included; intros. apply MKT19; eauto. }
      pose proof in_ω_2. pose proof H39. apply MKT164,MKT156 in H40
      as []. rewrite <-H41 in H39. apply H33 in H39; auto.
      elim H39. apply AxiomI; split; intros; elim (@ MKT16 z); auto.
      apply AxiomII in H42 as []. apply H43. apply MKT4; auto. }
    elim H23. rewrite H35. apply Filter_Extension1; auto.
    destruct H32. apply H24 in H32 as [H32 _].
    apply NEexE in H32 as []. apply NEexE. exists x0.
    apply MKT4; auto. pose proof H36. apply MKT69b in H36.
    rewrite H9b in H37. apply H9 in H37. apply MKT19 in H36.
    destruct H32. apply H24 in H32 as [_[H32 _]].
    unfold Included; intros. apply MKT4 in H39 as []; auto.
    apply MKT41 in H39; auto. rewrite H39. apply AxiomII; split;
    auto. unfold Included; intros. rewrite H37 in H40.
    apply AxiomII in H40; tauto. destruct H35.
    destruct H35 as [b[H35[_[]]]]. elim H23. rewrite H37.
    apply H24. destruct H32; auto. destruct H35.
    destruct (classic (\{ λ w, w ⊂ ω
     /\ Finite_Intersection (r[x1] ∪ [w])
     /\ (First φ[x1])「w」 ∩ (Second φ[x1])「w」 = Φ \} ∈ dom(c))).
    apply H10,AxiomII in H37 as [H38[H39[H40 _]]]. elim H23.
    rewrite H36. apply Filter_Extension1; auto.
    destruct H32. apply H24 in H32 as [H32 _].
    apply NEexE in H32 as []. apply NEexE. exists x0.
    apply MKT4; auto. unfold Included; intros.
    apply MKT4 in H37 as []. destruct H32.
    apply H24 in H32 as [_[]]; auto. apply MKT41 in H37; auto.
    apply AxiomII. rewrite H37; auto. apply MKT69a in H37.
    rewrite H37 in H36. pose proof MKT39. apply MKT43 in H38.
    rewrite H38,MKT20 in H36.
    pose proof (FilterBase_from_Fact μ).
    assert (μ = 〈μ〉→ᵇ).
    { apply AxiomI; split; intros; auto. apply MKT19; eauto. }
    rewrite <-H40 in H36. apply MKT69b in H21. rewrite H36 in H21.
    elim MKT39; eauto. destruct H32. rewrite H33 in H27.
    elim H23. rewrite H27. apply FilterBase_Property2.
    unfold Nest; intros v1 v2 H34 H35.
    assert (Function (r|(x))). { apply MKT126a; auto. }
    apply Einr in H34 as [u1[]]; auto. apply Einr in H35 as [u2[]];
    auto. rewrite MKT126c in H37,H38; auto. rewrite H29 in H34,H35.
    assert (Ordinal u1 /\ Ordinal u2) as [].
    { apply AxiomII in H26 as []. split; apply (MKT111 x); auto. }
    rewrite H37,H38. apply (@ MKT110 u1 u2) in H40 as [H40|[|]];
    try apply H18 in H40; auto. rewrite H40; auto.
    pose proof in_ω_0. pose proof H34. apply AxiomII in H35
    as [_[H35 _]]. apply AxiomII in H26 as [].
    apply (@ MKT110 x) in H35 as [H35|[|]]; auto.
    elim (@ MKT16 x); auto. rewrite <-H29 in H35.
    apply Property_Value,Property_ran in H35; auto.
    apply NEexE; eauto. apply MKT126a; auto. intros.
    apply Einr in H34 as [x0[]]. rewrite MKT126c in H35; auto.
    rewrite H29 in H34. apply H24 in H34. rewrite H35; auto.
    apply MKT126a; auto. }
  assert (∀ n, n ∈ dom(r) -> n ∈ P[pow(ω)] -> P[r[n]] = ω) as Hk.
  { intros. apply NNPP; intro.
    set (A := \{ λ u, u ∈ dom(r) /\ u ∈ P[pow(ω)]
      /\ P[r[u]] <> ω \}).
    assert (A ⊂ R /\ A <> Φ) as [].
    { split. unfold Included; intros. apply AxiomII in H23
      as [H23[]]. apply MKT111 in H24; auto. apply AxiomII; auto.
      apply NEexE. exists n. apply AxiomII; split; eauto. }
    pose proof MKT113a. apply MKT107 in H25 as [_].
    apply H25 in H23 as []; auto. clear H24 H25.
    destruct H23 as []. apply AxiomII in H23 as [H23[H25[H25']]].
    assert (∀ u, u ∈ x -> P[r[u]] = ω).
    { intros. apply NNPP; intro. assert (u ∈ A).
      { apply AxiomII; repeat split; eauto. destruct H14.
        apply H29 in H25; auto. apply Property_PClass in H0.
        apply AxiomII in H0 as [_[]]. apply AxiomII in H0 as [_[]].
        apply H30 in H25'; auto. }
      apply H24 in H29. elim H29. apply AxiomII'; split; auto.
      apply MKT49a; eauto. }
    assert (dom(r|(x)) = x).
    { destruct H14. apply H28,MKT30 in H25. rewrite MKT126b; auto. }
    assert (∀ u, u ∈ x -> r|(x)[u] = r[u]).
    { intros. rewrite MKT126c; auto. rewrite H28; auto. }
    assert ((r|(x)) ∈ dom(h)).
    { apply NNPP; intro. apply MKT69a in H30.
      assert (x ∈ R).
      { apply MKT111 in H25; auto. apply AxiomII; auto. }
      apply H15 in H31. apply Property_Value,Property_ran in H25;
      auto. elim MKT39. rewrite <-H30,<-H31; eauto. }
    apply Property_Value,AxiomII' in H30 as []; auto.
    rewrite H28 in H31. destruct H31. rewrite <-H15 in H32;
    [ |apply AxiomII; auto]. destruct H32 as [[]|[]].
    elim H26. rewrite H33. apply Existence_of_NPAUF_Lemma21.
    destruct H33 as [[x0[]]|[]]. rewrite H29 in H34;
    [ |destruct H33]; auto. assert (P[r[x0]] = ω).
    { apply H27; destruct H33; auto. }
    destruct H34 as [[]|[H34[[b[H36[H37[]]]]|[]]]].
    assert (Ensemble e[x0]).
    { apply NNPP; intro. apply MKT43 in H37.
      rewrite H37,MKT20 in H36.
      assert (r[x] = μ).
      { rewrite H36. apply AxiomI; split; intros. apply MKT19;
        eauto. apply FilterBase_from_Fact; auto. }
      apply MKT69b in H25. elim MKT39. rewrite <-H38; auto. }
    elim H26. rewrite H36. apply Existence_of_NPAUF_Lemma22.
    apply Existence_of_NPAUF_Lemma15; auto. left.
    apply finsin; auto. rewrite <-H39 in H35; auto.
    assert (Ensemble c[\{ λ w, w ⊂ ω /\ Finite_Intersection (r[x0]
       ∪[w]) /\ (First φ[x0])「w」 ∩ (Second φ[x0])「w」 = Φ \}]).
    { apply NNPP; intro. apply MKT43 in H36.
      rewrite H36,MKT20 in H39.
      assert (r[x] = μ).
      { rewrite H39. apply AxiomI; split; intros. apply MKT19;
        eauto. apply FilterBase_from_Fact; auto. }
      apply MKT69b in H25. elim MKT39. rewrite <-H37; auto. }
    elim H26. rewrite H39. apply Existence_of_NPAUF_Lemma22.
    apply Existence_of_NPAUF_Lemma15; auto. left.
    apply finsin; auto.
    assert (Function (r|(x))). { apply MKT126a; auto. }
    apply MKT160 in H35; [ |apply MKT75; auto; rewrite H28; auto].
    rewrite H28 in H35. assert (P[x] ≼ x).
    { apply MKT157; auto. apply MKT111 in H25; auto.
      apply AxiomII; auto. }
    assert (P[ran(r|(x))] ≼ x).
    { destruct H35,H36; unfold LessEqual; try rewrite H35; auto.
      destruct H31. apply H37 in H36; auto.
      rewrite H36 in H35; auto. }
    assert (P[ran(r|(x))] ∈ P[pow(ω)]).
    { destruct H37; try rewrite H37; auto. apply Property_PClass,
      AxiomII in H0 as [_[H0 _]]. apply AxiomII in H0 as [_[_]].
      apply H0 in H25'; auto. }
    assert (P[ran(r|(x))] ≼ ω).
    { assert (P[ran(r|(x))] ∈ C).
      { apply Property_PClass,AxiomV;
        [apply MKT126a|rewrite H28]; auto. }
      assert (Ordinal ω /\ Ordinal P[ran(r|(x))]) as [].
      { pose proof MKT138. apply AxiomII in H39 as [_[H39 _]].
        apply AxiomII in H39 as [_]. apply AxiomII in H40; tauto. }
      apply (@ MKT110 ω) in H41 as [H41|[|]]; unfold LessEqual;
      auto. apply CH in H41 as []; auto.
      elim (MKT102 P[pow(ω)] P[ran(r|(x))]); auto.
      rewrite <-H41 in H38. elim (MKT101 P[pow(ω)]); auto. }
    assert (∀ a, a ∈ ran(r|(x)) -> P[a] = ω).
    { intros. apply Einr in H40 as [u[]]; [ |apply MKT126a; auto].
      rewrite MKT126c in H41; auto. rewrite H41. apply H27.
      rewrite MKT126b in H40; auto. apply MKT4' in H40; tauto. }
    elim H26. rewrite H34. destruct H39.
    apply Existence_of_NPAUF_Lemma17; auto. apply NEexE in H32
    as []. apply NEexE. exists r[x0]. rewrite <-(MKT126c _ x);
    [ | |rewrite H28]; auto. apply (@ Property_ran x0),
    Property_Value; auto. apply MKT126a; auto. rewrite H28; auto.
    apply Existence_of_NPAUF_Lemma14; auto. }
  assert (P[pow(ω)] ⊂ dom(r)).
  { pose proof H3. apply (@ MKT109 dom(r)) in H20 as []; auto.
    destruct (classic (dom(r) = Φ)). pose proof (@ MKT16 Φ).
    rewrite <-H21 in H22. apply MKT69a in H22.
    rewrite H21,H17 in H22. destruct (Fσ_is_just_Filter ω).
    unfold Finite. rewrite Inf_P1. apply MKT101. New MKT138; eauto.
    apply Filter_is_Set_Fact2 in H23. rewrite H22 in H23. elim MKT39; eauto.
    assert (dom(r) ∈ R).
    { apply AxiomII; split; auto. apply MKT33 in H20; eauto. }
    assert (dom(r|(dom(r))) = dom(r)).
    { rewrite MKT126b; auto. rewrite MKT5'; auto. }
    pose proof H22. apply H15 in H24. pose proof (MKT101 dom(r)).
    apply MKT69a in H25.
    destruct (classic (∃ x, LastMember x E dom(r))) as [[x]|].
    assert (x ∈ P[pow(ω)]). { destruct H26; auto. }
    assert ((r|(dom(r)))[x] = r[x]).
    { apply MKT126c; auto. rewrite H23. destruct H26; auto. }
    pose proof H27. apply H9 in H29. pose proof H27.
    apply H7 in H30 as [H30[]]. pose proof H27.
    apply H8 in H33 as [H33[]]. pose proof H27.
    rewrite <-H9b in H36. apply MKT69b,MKT19 in H36.
    destruct (classic (Finite_Intersection (r[x] ∪ [e[x]]))).
    assert (FilterBase (〈r[x] ∪ [e[x]]〉→ᵇ) ω).
    { apply Filter_Extension1; auto. destruct H26.
      apply H19 in H26 as []. apply NEexE in H26 as [].
      apply NEexE. exists x0. apply MKT4; auto. destruct H26.
      apply H19 in H26 as [_[H26 _]]. unfold Included; intros.
      apply MKT4 in H39 as []; auto. apply MKT41 in H39; auto.
      rewrite H39. apply AxiomII; split; auto. rewrite H29.
      unfold Included; intros. apply AxiomII in H40; tauto. }
    pose proof H38. apply FilterBase_is_Set in H39.
    assert ([r|(dom(r)),〈r[x] ∪ [e[x]]〉→ᵇ] ∈ h).
    { apply AxiomII'; split. apply MKT49a; auto. rewrite H23.
      split; auto. right. split; auto. left. exists x.
      split; auto. left. rewrite H28; auto. }
    apply Property_dom,MKT69b in H40. rewrite <-H24,H25 in H40.
    elim MKT39; eauto. New MKT138. eauto. destruct (classic (∃ b, Finite b
      /\ b ⊂ ω /\ (First φ[x])⁻¹「(Second φ[x])「b」」
       ∪ (Second φ[x])⁻¹「(First φ[x])「b」」 ∈ 〈r[x]〉→ᶠ)).
    assert ([r|(dom(r)),r[x]] ∈ h).
    { apply AxiomII'; split. apply MKT49a; auto. destruct H26.
      apply MKT69b in H26; auto. rewrite H23. split; auto. right.
      split; auto. left. exists x. split; auto. right. rewrite H28.
      split; auto. left. destruct H38 as [b[H38[]]]. eauto. }
    apply Property_Fun in H39; auto. rewrite <-H24,H25 in H39.
    destruct H26. apply MKT69b in H26. rewrite H39 in H26.
    elim MKT39; eauto.
    assert (∀ b, Finite b -> b ⊂ ω
      -> ((First φ[x])⁻¹「(Second φ[x])「b」」
       ∪ (Second φ[x])⁻¹「(First φ[x])「b」」) ∉ 〈r[x]〉→ᶠ).
    { intros. intro. elim H38; eauto. } clear H38.
    destruct H26. pose proof H26. apply H19 in H40.
    pose proof H40. apply FilterBase_Property1 in H41.
    pose proof H41. apply (Filter_Extension_1_and_2 _ ω) in H42
    as []; eauto; [ |destruct H40|destruct H40 as [H40[]]]; auto.
    assert (∃ a, a ∈ r[x] /\ a ∩ e[x] = Φ) as [a[]].
    { apply NNPP; intro. assert (∀ a, a ∈ r[x] -> a ∩ e[x] <> Φ).
      { intros; intro. elim H44; eauto. }
      elim H37. unfold Finite_Intersection; intros.
      destruct (classic (e[x] ∈ A)).
      assert (∩A = (∩(A ~ [e[x]])) ∩ e[x]).
      { apply AxiomI; split; intros. apply AxiomII in H49 as [].
        apply MKT4'; split. apply AxiomII; split; auto; intros.
        apply H50. apply MKT4' in H51; tauto. apply H50; auto.
        apply MKT4' in H49 as []. apply AxiomII in H49 as [].
        apply AxiomII; split; auto; intros.
        destruct (classic (y = e[x])). rewrite H53; auto.
        apply H51. apply MKT4'; split; auto. apply AxiomII; split;
        eauto. intro. apply MKT41 in H54; auto. }
      assert ((A ~ [e[x]]) ⊂ r[x]).
      { unfold Included; intros. apply MKT4' in H50 as [].
        apply H46,MKT4 in H50 as []; auto.
        apply AxiomII in H51 as []. elim H52; auto. }
      assert (Finite (A ~ [e[x]])).
      { assert ((A ~ [e[x]]) ⊂ A).
        { unfold Included; intros. apply MKT4' in H51; tauto. }
        apply MKT158 in H51 as []. pose proof MKT138.
        apply AxiomII in H52 as [_[]]. apply H53 in H47.
        apply H47; auto. unfold Finite. rewrite H51; auto. }
      destruct (classic ((A ~ [e[x]]) = Φ)).
      rewrite H52,MKT24,MKT6',MKT20' in H49. destruct H40.
      apply NEexE in H40 as []. apply H45 in H40. intro.
      elim H40. rewrite <-H49,H54,MKT6',MKT17'; auto.
      rewrite H49. apply H45,Existence_of_NPAUF_Lemma5; auto.
      destruct H40 as [_[_[]]]; auto.
      assert (A ⊂ r[x]).
      { unfold Included; intros. pose proof H49. apply H46,MKT4
        in H49 as []; auto. apply MKT41 in H49; auto.
        rewrite H49 in H50. elim H48; auto. }
      apply H41; auto. }
    assert (a ⊂ \{ λ u, u ∈ ω
      /\ (First φ[x])[u] <> (Second φ[x])[u] \}).
    { unfold Included; intros. apply NNPP; intro.
      elim (@ MKT16 z). rewrite <-H45. apply MKT4'; split; auto.
      assert (z ∈ ω).
      { apply H42 in H44. destruct H43 as [H43 _].
        apply H43,AxiomII in H44 as []; auto. }
      rewrite H29. apply AxiomII; repeat split; eauto.
      apply NNPP; intro. elim H47. apply AxiomII; split; eauto. }
    assert (\{ λ u, u ∈ ω /\ (First φ[x])[u] <> (Second φ[x])[u] \}
       ∈ 〈r[x]〉→ᶠ).
    { destruct H43 as [H43[_[_[]]]]. apply H48 in H46; auto.
      unfold Included; intros. apply AxiomII in H49; tauto. }
    apply Existence_of_NPAUF_Lemma7 in H47 as [b[H47[]]]; auto.
    assert (\{ λ w, w ⊂ ω /\ Finite_Intersection (r[x] ∪ [w])
      /\ (First φ[x])「w」 ∩ (Second φ[x])「w」 = Φ \} ∈ dom(c)).
    { assert (Ensemble (\{ λ w, w ⊂ ω
        /\ Finite_Intersection (r[x] ∪ [w])
        /\ (First φ[x])「w」 ∩ (Second φ[x])「w」 = Φ \})).
      { apply (MKT33 pow(ω)); auto. unfold Included; intros.
        apply AxiomII in H50 as [H50[]]. apply AxiomII; auto. }
      rewrite H11. apply MKT4'; split. apply MKT19; auto.
      apply AxiomII; split; auto. intro. apply MKT41 in H51; auto.
      elim (@ MKT16 b). rewrite <-H51. apply AxiomII; split; auto.
      apply (MKT33 ω); auto. }
    apply H10,AxiomII in H50 as [H50[H51[H52 _]]].
    apply (Filter_Extension1 _ ω) in H52 as []; auto.
    apply FilterBase_is_Set in H53; eauto.
    assert ([r|(dom(r)),〈r[x] ∪ [c[\{ λ w, w ⊂ ω
      /\ Finite_Intersection (r[x] ∪ [w])
      /\ (First φ[x])「w」 ∩ (Second φ[x])「w」 = Φ \}]]〉→ᵇ] ∈ h).
    { apply AxiomII'; split. apply MKT49a; auto. rewrite H23.
      split; auto. right. split; auto. left. exists x. split.
      split; auto. right. rewrite H28. split; auto. }
    apply Property_Fun in H54; auto. rewrite H54,<-H24,H25 in H53.
    elim MKT39; auto. apply NEexE. exists a. apply MKT4; auto.
    unfold Included; intros. apply AxiomII; split; eauto.
    destruct H40 as [_[]]. apply MKT4 in H53 as [].
    apply H40,AxiomII in H53 as []; auto. apply MKT41 in H53; auto.
    rewrite H53; auto.
    assert (Ordinal Φ /\ Ordinal x) as [].
    { apply MKT111 in H27; auto. pose proof in_ω_0.
      apply AxiomII in H48 as [_[]]; auto. }
    rewrite <-H17. apply (@ MKT110 Φ) in H49 as [H49|[|]]; auto.
    elim (@ MKT16 x); auto. rewrite H49; auto.
    assert (Ensemble (∪ran(r|(dom(r))))).
    { apply AxiomVI,AxiomV. apply MKT126a; auto.
      rewrite H23; eauto. }
    assert ([r|(dom(r)),(∪ran(r|(dom(r))))] ∈ h).
    { apply AxiomII'; split; auto. rewrite H23. split; auto. }
    apply Property_Fun in H28; auto. rewrite H28,<-H24,H25 in H27.
    elim MKT39; auto. }
  assert (Function (r|(P[pow(ω)]))). { apply MKT126a; auto. }
  assert (dom(r|(P[pow(ω)])) = P[pow(ω)]).
  { rewrite MKT126b; auto. apply MKT30; auto. }
  assert (FilterBase (∪ran(r|(P[pow(ω)]))) ω).
  { apply FilterBase_Property2. unfold Nest; intros.
    apply Einr in H23 as [x0[]]; auto.
    apply Einr in H24 as [y0[]]; auto.
    rewrite MKT126c in H25,H26; auto. rewrite H22 in H23,H24.
    assert (Ordinal x0 /\ Ordinal y0) as [].
    { apply MKT111 in H23,H24; auto. }
    rewrite H25,H26. apply (@ MKT110 x0) in H28 as [H28|[|]]; auto.
    rewrite H28; auto. apply NEexE. exists r[Φ].
    assert (Φ ∈ dom(r|(P[pow(ω)]))).
    { rewrite H22. pose proof H. apply MKT161 in H23.
      destruct H3. apply H24 in H23. apply H23. pose proof MKT165.
      apply MKT156 in H25 as []. rewrite H26; auto. }
    rewrite <-(MKT126c r (P[pow(ω)])); auto.
    apply (@ Property_ran Φ),Property_Value; auto.
    intros. apply Einr in H23 as [x[]]; auto. rewrite H24,MKT126c;
    auto. apply H19. rewrite H22 in H23; auto. }
  pose proof H23. destruct H24 as [H24[]].
  apply FilterBase_Property1,(Filter_Extension_1_and_2 _ ω) in H23
  as []; auto. clear H24 H25 H26.
  apply Filter_Extension3 in H27 as [p[]]; auto.
  assert (∀ n, p <> F n).
  { intros. destruct (classic (n ∈ ω)). apply FT2_a in H26 as [_]; eauto.
    intro. elim H26. rewrite <-H27. apply Fσ_and_free_ultrafilter; auto.
    unfold Finite. rewrite Inf_P1. apply MKT101.
    unfold Included; intros. apply H24,H23. apply AxiomII;
    split; eauto. exists Fσ. split; auto. rewrite <-H17.
    assert (Φ ∈ dom(r|(P[pow(ω)]))).
    { rewrite H22. pose proof H. apply MKT161 in H29.
      destruct H3. apply H30 in H29. apply H29. pose proof MKT165.
      apply MKT156 in H31 as []. rewrite H32; auto. }
    rewrite <-(MKT126c r (P[pow(ω)])); auto.
    apply (@ Property_ran Φ),Property_Value; auto.
    apply Fa_P1 in H26. intro. rewrite H27,H26 in H25.
    destruct H25 as [[_[_[]]]]. elim (@ MKT16 ω); auto. }
  exists p. split; auto. clear H26.
  assert (∀ n, n ∈ P[pow(ω)] -> r[n] ⊂ p).
  { intros. rewrite <-H22 in H26. unfold Included; intros.
    apply H24,H23. apply AxiomII; split; eauto. exists r[n].
    split; auto. rewrite <-(MKT126c r (P[pow(ω)])); auto.
    apply (@ Property_ran n),Property_Value; auto. }
  split. unfold Finite. rewrite Inf_P1. apply MKT101.
  split; intros. apply βA_P1; auto.
  assert (Ensemble f /\ Ensemble g) as [].
  { split; apply MKT75; auto; [rewrite H29|rewrite H30]; auto. }
  assert ([f,g] ∈ ran(φ)).
  { rewrite H6. apply AxiomII'; split; auto.
    split; apply AxiomII; auto. } apply Einr in H36 as [n[]]; auto.
  assert (First φ[n] = f /\ Second φ[n] = g) as [].
  { rewrite <-H37; split; [rewrite MKT54a|rewrite MKT54b]; auto. }
  split; auto. split; auto. repeat split; auto.
  apply βA_P1; auto. pose proof H36. rewrite H5 in H40.
  pose proof H40. apply H9 in H41. rewrite <-H38,<-H39,<-H41.
  pose proof H40. rewrite <-H9b in H42. apply MKT69b,MKT19 in H42.
  pose proof H40. apply Existence_of_NPAUF_Lemma13 in H43.
  assert (Ordinal (PlusOne n)). { apply MKT111 in H43; auto. }
  assert (dom(r|(PlusOne n)) = PlusOne n).
  { rewrite MKT126b; auto. apply MKT30. destruct H14.
    apply H45; auto. }
  assert ((r|(PlusOne n))[n] = r[n]).
  { apply MKT126c; auto. rewrite H45. apply MKT4; right.
    apply MKT41; eauto. }
  assert (LastMember n E (PlusOne n)).
  { apply Existence_of_NPAUF_Lemma12. apply AxiomII; split; eauto.
    apply MKT111 in H40; auto. }
  assert ((PlusOne n) ∈ R). { apply AxiomII; split; eauto. }
  apply H15 in H48. assert ((r|(PlusOne n)) ∈ dom(h)).
  { apply NNPP; intro. apply MKT69a in H49. apply H20,MKT69b in H43.
    rewrite H48,H49 in H43. elim MKT39; auto. }
  apply Property_Value,AxiomII' in H49 as [_[_[]]]; auto.
  destruct H49. rewrite H45 in H49. elim (@ MKT16 n).
  rewrite <-H49. apply MKT4; right. apply AxiomII; split; eauto.
  destruct H49 as [_[[m]|]]. rewrite H45 in H49. destruct H49.
  assert (m = n).
  { destruct H47,H49. assert (Ordinal m /\ Ordinal n) as [].
    { apply MKT111 in H47,H49; auto. }
    apply (@ MKT110 m) in H54 as [H54|[]]; auto.
    apply H52 in H47. elim H47. apply AxiomII'; split.
    apply MKT49a; eauto. apply AxiomII'; split; auto.
    apply MKT49a; eauto. pose proof H49. apply H51 in H49.
    elim H49. apply AxiomII'; split. apply MKT49a; eauto.
    apply AxiomII'; split; auto. apply MKT49a; eauto. }
  rewrite H51 in *. clear dependent m.
  rewrite H46,<-H48,H38,H39 in H50. destruct H50 as [[]|[]].
  apply (H26 (PlusOne n)); auto. rewrite H51.
  apply FilterBase_from_Fact. apply MKT4; auto.
  destruct H51 as [[b[H51[H52[]]]]|[]]. pose proof H40.
  apply H20,H19 in H55. pose proof H55.
  destruct H56 as [H56[H57[]]].
  apply FilterBase_Property1,(Filter_Extension_1_and_2 _ ω) in H55 as []; auto.
  pose proof H53. apply AxiomII in H61 as [_[H61[A[H62[]]]]].
  assert (∩A ∈ r[n]).
  { apply Existence_of_NPAUF_Lemma5; auto. intro.
    rewrite H65,MKT24 in H64. assert (ω = μ).
    { apply AxiomI; split; intros; auto. apply MKT19; eauto. }
    elim MKT39. rewrite <-H66; auto. }
  assert ((f⁻¹「g「b」」 ∪ g⁻¹「f「b」」) ∈ p).
  { destruct H25 as [[_[_[_[_]]]]_]. apply (H25 (∩A)); auto.
    apply (H26 n); auto. }
  apply (FT1 _ ω) in H66; auto. apply Existence_of_NPAUF_Lemma2 in H33;
  eauto. destruct H33 as [_[_[_[_[_[_[_]]]]]]].
  rewrite H41,H38,H39; auto. apply βA_P1; auto.
  assert (\{ λ w, w ⊂ ω /\ Finite_Intersection (r[n] ∪ [w])
    /\ f「w」 ∩ g「w」 = Φ \} ∈ dom(c)).
  { apply NNPP; intro. apply MKT69a in H53. pose proof MKT39.
    apply MKT43 in H54. rewrite H53,H54,MKT20 in H52.
    pose proof (FilterBase_from_Fact μ).
    assert (〈μ〉→ᵇ = μ).
    { apply AxiomI; split; intros; auto. apply MKT19; eauto. }
    apply H20,MKT69b in H43. rewrite H52,H56 in H43.
    elim MKT39; eauto. }
  apply H10,AxiomII in H53 as [H53[H54[]]].
  apply Existence_of_NPAUF_Lemma3 in H33; auto. destruct H33.
  apply βA_P1; auto. exists (c[\{ λ w, w ⊂ ω
    /\ Finite_Intersection (r[n] ∪ [w]) /\ f「w」 ∩ g「w」 = Φ \}]).
  split; auto. apply (H26 (PlusOne n)); auto. rewrite H52.
  apply FilterBase_from_Fact,MKT4; auto. destruct H49.
  elim H49. rewrite H45; eauto.
Qed.





