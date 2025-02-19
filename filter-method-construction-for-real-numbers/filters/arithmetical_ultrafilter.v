(*       This file presents the formalization of the concept of      *)
(*                  arithmetical ultrafilter (AUF).                  *)
(*  It is developmented in the CoqIDE (version 8.13.2) for windows.  *)

(** arithmetical_ultrafilter *)

Require Export filters.filter.

Declare Scope filter_scope.
Delimit Scope filter_scope with fi.
Open Scope filter_scope.

(* Def: image set of f at A  *)
Definition ImageSet f A := \{ λ u, ∃ m, u = f[m] /\ m ∈ A \}.

Notation "f 「 A 」" := (ImageSet f A)(at level 5) : filter_scope.

(* Def: preimage set of f at A  *)
Definition PreimageSet f A := \{ λ u, u ∈ dom(f) /\ f[u] ∈ A \}.

Notation "f ⁻¹「 A 」" := (PreimageSet f A)(at level 5) : filter_scope.

Fact ImageSet_Fact : ∀ f A, Function f
  -> A ∩ dom(f) <> Φ <-> f「A」 <> Φ.
Proof.
  split; intros.
  - intro. elim H0. apply AxiomI; split; intros.
    + apply MKT4' in H2 as [].
      assert (f[z] ∈ f「A」).
      { apply AxiomII. apply Property_Value,Property_ran
        in H3; auto. split; eauto. }
      rewrite H1 in H4. elim (@ MKT16 f[z]); auto.
    + elim (@ MKT16 z); auto.
  - intro. elim H0. apply AxiomI; split; intros; elim
    (@ MKT16 z); auto. apply AxiomII in H2 as [H2[x[]]].
    assert (x ∈ (A ∩ dom(f))).
    { apply MKT4'; split; auto. apply NNPP; intro.
      apply MKT69a in H5. rewrite H3,H5 in H2. elim
      MKT39; auto. }
    rewrite H1 in H5. elim (@ MKT16 x); auto.
Qed.

Fact PreimageSet_Fact : ∀ f A, Function f
  -> A ∩ ran(f) <> Φ <-> f⁻¹「A」 <> Φ.
Proof.
  split; intros.
  - intro. elim H0.
    apply AxiomI; split; intros; elim (@ MKT16 z); auto.
    apply MKT4' in H2 as []. apply AxiomII in H3 as [H3[]].
    assert (x ∈ f⁻¹「A」).
    { apply AxiomII. pose proof H4.
      apply Property_dom,Property_Value in H5; auto.
      assert (z = f[x]). { destruct H. apply (H6 x); auto. }
      rewrite H6 in H2. apply Property_dom in H4. split; eauto. }
    rewrite H1 in H5. elim (@ MKT16 x); auto.
  - intro. elim H0.
    apply AxiomI; split; intros; elim (@ MKT16 z); auto.
    apply AxiomII in H2 as [H2[]].
    assert (f[z] ∈ (A ∩ ran(f))).
    { apply MKT4'; split; auto.
      apply Property_Value,Property_ran in H3; auto. }
    rewrite H1 in H5. elim (@ MKT16 f[z]); auto.
Qed.

(* some properties about image and preimage sets *)
Property ImageSet_Property1 : ∀ f A B, f⁻¹「A ∪ B」 = f⁻¹「A」 ∪ f⁻¹「B」.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]]. apply MKT4.
    apply MKT4 in H1 as []; [left|right]; apply AxiomII; auto.
  - apply AxiomII; split. eauto. apply MKT4 in H as [].
    apply AxiomII in H as [H[]]. split; auto. apply MKT4; auto.
    apply AxiomII in H as [H[]]. split; auto. apply MKT4; auto.
Qed.

Property ImageSet_Property2 : ∀ f A B, f⁻¹「A ∩ B」 = f⁻¹「A」 ∩ f⁻¹「B」.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]]. apply MKT4' in H1 as [].
    apply MKT4'; split; apply AxiomII; auto.
  - apply MKT4' in H as []. apply AxiomII in H as [H[]].
    apply AxiomII in H0 as [H0[]]. apply AxiomII.
    repeat split; auto. apply MKT4'; auto.
Qed.

Property ImageSet_Property3 : ∀ f A B, f「A ∩ B」 ⊂ (f「A」 ∩ f「B」).
Proof.
  intros. unfold Included; intros. apply AxiomII in H as [H[x[]]].
  apply MKT4' in H1 as []. apply MKT4'; split. apply AxiomII.
  split; eauto. apply AxiomII. split; eauto.
Qed.

Property ImageSet_Property4 : ∀ f A B, f⁻¹「A ~ B」 = f⁻¹「A」 ~ f⁻¹「B」.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]]. apply MKT4' in H1 as [].
    apply AxiomII in H2 as []. apply MKT4'; split.
    apply AxiomII; auto. apply AxiomII. split; auto. intro.
    apply AxiomII in H4 as [H4[]]. contradiction.
  - apply MKT4' in H as []. apply AxiomII in H as [H[]].
    apply AxiomII in H0 as []. apply AxiomII. repeat split; auto.
    apply MKT4'; split; auto. apply AxiomII; split. eauto. intro.
    elim H3. apply AxiomII; auto.
Qed.

Property ImageSet_Property5 : ∀ f A B, (f「A」 ~ f「B」) ⊂ f「A ~ B」.
Proof.
  intros. unfold Included; intros. apply MKT4' in H as [].
  apply AxiomII in H as [H[x[]]]. apply AxiomII in H0 as [].
  apply AxiomII; split; auto. exists x. split; auto. apply MKT4'.
  split; auto. apply AxiomII; split. eauto. intro. elim H3.
  apply AxiomII; split; eauto.
Qed.

Property ImageSet_Property6 : ∀ f A, A ⊂ dom(f) -> A ⊂ f⁻¹「f「A」」.
Proof.
  intros. unfold Included; intros. apply AxiomII; split. eauto.
  split. apply H; auto. apply AxiomII. split; eauto.
  apply MKT19,MKT69b. apply H; auto.
Qed.

Property ImageSet_Property7 : ∀ f A, Function1_1 f -> A ⊂ dom(f)
  -> A = f⁻¹「f「A」」.
Proof.
  intros. apply MKT27; split. apply ImageSet_Property6; auto.
  unfold Included; intros. apply AxiomII in H1 as [H1[]].
  apply AxiomII in H3 as [H3[x[]]]. destruct H.
  apply f11inj in H4; try rewrite H4; auto.
Qed.

Property ImageSet_Property8_a : ∀ f A, f「f⁻¹「A」」 ⊂ A.
Proof.
  intros. unfold Included; intros. apply AxiomII in H as [H[x[]]].
  apply AxiomII in H1 as [H1[]]. rewrite H0; auto.
Qed.

Property ImageSet_Property8_b : ∀ f A, Function f -> A ⊂ ran(f)
  -> f「f⁻¹「A」」 = A.
Proof.
  intros. apply MKT27; split. apply ImageSet_Property8_a.
  unfold Included; intros. apply AxiomII; split. eauto.
  pose proof H1 as H1'. apply H0 in H1.
  apply AxiomII in H1 as [H1[]]. pose proof H2.
  apply Property_dom in H3. apply Property_Value in H3; auto.
  exists x. assert (z = f[x]). { destruct H. apply (H4 x); auto. }
  split; auto. apply AxiomII. apply Property_dom in H2.
  rewrite H4 in H1'. split; eauto.
Qed.

Property ImageSet_Property9_a : ∀ f, Function f -> f「dom(f)」 = ran(f).
Proof.
  intros. apply AxiomI; split; intros. apply AxiomII in H0 as [H0[x[]]].
  rewrite H1. apply (@ Property_ran x); auto. apply Property_Value; auto.
  apply AxiomII; split. eauto. apply AxiomII in H0 as [H0[]]. New H1.
  apply Property_dom in H1. apply Property_Fun in H2; eauto.
Qed.

Property ImageSet_Property9_b : ∀ f, Function f -> f⁻¹「ran(f)」 = dom(f).
Proof.
  intros. apply AxiomI; split; intros. apply AxiomII in H0 as [H0[]]; auto.
  apply AxiomII in H0 as [H0[]]. apply AxiomII; split; auto. New H1.
  apply Property_dom in H1. apply Property_Fun in H2; auto.
  split; auto. apply (@ Property_ran z),Property_Value; auto.
Qed.

(* value of comparison functions *)
Lemma ImageSet_Property10_Lemma : ∀ f g a, Function f -> (g ∘ f)[a] = g[f[a]].
Proof.
  intros. destruct (classic (a ∈ dom(f))).
  - apply AxiomI; split; intros.
    + apply AxiomII in H1 as []. apply AxiomII; split; auto. intros.
      apply AxiomII in H3 as []. apply H2,AxiomII; split; auto.
      apply AxiomII'; split. apply MKT49a; eauto. exists (f[a]).
      split; auto. apply Property_Value; auto.
    + apply AxiomII in H1 as []. apply AxiomII; split; auto. intros.
      apply AxiomII in H3 as []. apply H2,AxiomII; split; auto.
      apply AxiomII' in H4 as [H4[x0[]]]. pose proof H5.
      apply Property_dom,Property_Value in H7; auto.
      replace (f[a]) with x0; auto. destruct H. apply (H8 a); auto.
  - pose proof H0 as Ha. apply MKT69a in H0. rewrite H0.
    assert (μ ∉ dom(g)). { intro. elim MKT39; eauto. }
    apply MKT69a in H1. rewrite H1. apply AxiomI; split; intros.
    apply MKT19. eauto. apply AxiomII; split. eauto. intros.
    apply AxiomII in H3 as []. apply AxiomII' in H4 as [_[x[]]].
    apply Property_dom in H4. elim Ha; auto.
Qed.

(* image and preimage sets of comparison functions *)
Property ImageSet_Property10_a : ∀ f g A, Function f -> (g ∘ f)「A」 = g「f「A」」.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H0 as [H0[x[]]].
    rewrite ImageSet_Property10_Lemma in H1; auto.
    destruct (classic (x ∈ dom(f))). apply AxiomII; split; auto.
    exists f[x]. split; auto. apply AxiomII; split; eauto. exists ran(f).
    apply (@ Property_ran x),Property_Value; auto. apply MKT69a in H3.
    rewrite H3 in H1. rewrite H1,MKT69a in H0. elim MKT39; auto.
    intro. elim MKT39; eauto.
  - apply AxiomII in H0 as [H0[x[]]]. apply AxiomII in H2 as [H2[x0[]]].
    apply AxiomII; split; auto. exists x0. split; auto.
    rewrite ImageSet_Property10_Lemma,<-H3; auto.
Qed.

Property ImageSet_Property10_b : ∀ f g A, Function f -> Function g
  -> (f ∘ g)⁻¹「A」 = g⁻¹「f⁻¹「A」」.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H1 as [H1[]]. apply AxiomII; split; auto.
    apply AxiomII in H2 as [H2[]]. apply AxiomII' in H4 as
    [H4[x1[]]]. split. apply Property_dom in H5; auto.
    apply AxiomII. pose proof H5 as Ha.
    apply Property_dom,Property_Value in Ha; auto.
    assert (x1 = g[z]). { destruct H0. apply (H7 z); auto. }
    apply Property_dom in H6. rewrite H7 in H6.
    repeat split; eauto. rewrite <-ImageSet_Property10_Lemma; auto.
  - apply AxiomII in H1 as [H1[]]. apply AxiomII in H3 as [H3[]].
    apply AxiomII; split; auto. rewrite ImageSet_Property10_Lemma; auto.
    split; auto. apply AxiomII; split; auto. exists (f[g[z]]).
    apply AxiomII'; split. apply MKT49a; eauto. exists (g[z]).
    split. apply Property_Value; auto. apply Property_Value; auto.
Qed.

(* filter Theo3: a method to judge if F is an ultrafilter over A   *)
Theorem FT3 : ∀ F A, ultraFilter F A <->
  F ⊂ pow(A) /\ Φ ∉ F
  /\ (∀ a b, a ∈ F -> b ∈ F -> (a ∩ b) ∈ F)
  /\ (∀ a, a ⊂ A -> a ∈ F \/ (A ~ a) ∈ F).
Proof.
  split; intros. destruct H as [[H[H0[H1[]]]]].
  repeat split; auto. destruct H as [H[H0[]]].
  assert (Φ ⊂ A).
  { unfold Included; intros. pose proof (@ MKT16 z). contradiction. }
  apply H2 in H3 as []; try contradiction. repeat split; auto.
  replace A with (A ~ Φ); auto. apply AxiomI; split; intros.
  apply MKT4' in H4; tauto. apply MKT4'; split; auto.
  apply AxiomII; split; eauto. intro. elim (@ MKT16 z); auto.
  intros. apply NNPP; intro. apply H2 in H5 as []; auto.
  assert ((a ∩ (A ~ b)) ∈ F). { apply H1; auto. }
  replace (a ∩ (A ~ b)) with Φ in H8; auto.
  apply AxiomI; split; intros. elim (@ MKT16 z); auto.
  apply MKT4' in H9 as []. apply MKT4' in H10 as [].
  apply AxiomII in H11 as []. elim H12; auto.
Qed.

(* Def: βA is the set consisting all ultrafilters over A;
        it is called the ultrafilter space over A  *)
Definition β A := \{ λ u, ultraFilter u A \}.

Fact βA_is_Set : ∀ A, Ensemble (β A).
Proof. (*此因 βA ⊂ pow(pow(A)) *)
  intros. destruct (classic (Ensemble A)). apply (MKT33 (pow(pow(A)))).
  repeat apply MKT38a; auto. pose proof MKT138; eauto. unfold Included;
  intros. apply AxiomII in H1 as [H1[[]]]. apply AxiomII; auto.
  assert (β A = Φ).
  { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
    apply AxiomII in H0 as [_[]]. elim H. eauto with Fi. }
  rewrite H0. eauto.
Qed.

Property βA_P1 : ∀ F A, F ∈ (β A) <-> ultraFilter F A.
Proof.
  split; intros. apply AxiomII in H; tauto.
  apply AxiomII; split; auto. destruct H. eauto with Fi.
Qed.

Property βA_P2 : ∀ A, (β A) = Φ <-> ((~ Ensemble A) \/ A = Φ).
Proof.
  split; intros. apply NNPP; intro. apply notandor in H0 as [].
  apply ->NNPP in H0. apply NEexE in H1 as [a]. assert ((F A a) ∈ (β A)).
  { assert (ultraFilter (F A a) A). apply Fa_P2_b; auto.
    apply AxiomII; split; auto. destruct H2. eauto with Fi. }
  rewrite H in H2. eapply MKT16; eauto. apply NNPP; intro.
  apply NEexE in H0 as []. apply AxiomII in H0 as [H0[]]. pose proof H1.
  apply Filter_is_Set_Fact1 in H3. destruct H; auto. destruct H1 as [_[H1[]]].
  rewrite H in H4; auto.
Qed.

(* Def: Transformation of ultrafilters  *)
Definition Transform F f B := \{ λ u, u ⊂ B /\ f⁻¹「u」 ∈ F \}.

Notation "f 〈 F ∣ B 〉" := (Transform F f B)(at level 5) : filter_scope.

(* each ultrafilter F over A can be transformed to an ultrafilter over B
   by a function f (A → B, i.e., domain f is A and range f contained in B)
   in the manner above (f〈F∣B〉)             *)
Theorem FT4 : ∀ F f A B, F ∈ (β A) -> Function f
  -> dom(f) = A -> ran(f) ⊂ B -> Ensemble B -> f〈F∣B〉 ∈ (β B).
Proof.
  intros. assert (ultraFilter (f〈F∣B〉) B).
  { apply FT3. apply AxiomII in H as [H[[H4[H5[H6[]]]]]].
    repeat split; intros.
    - unfold Included; intros.
      apply AxiomII in H10 as [H10[]]. apply AxiomII; auto.
    - intro. apply AxiomII in H10 as [H10[]].
      assert (f⁻¹「Φ」 = Φ).
      { apply AxiomI; split; intros.
        apply AxiomII in H13 as [H13[]].
        elim (@ MKT16 f[z]); auto. elim (@ MKT16 z); auto. }
      rewrite H13 in H12. contradiction.
    - apply AxiomII in H10 as [H10[]]. apply AxiomII in H11 as [H11[]].
      apply AxiomII; split. apply (MKT33 a); auto.
      unfold Included; intros. apply MKT4' in H16; tauto. split.
      unfold Included; intros. apply MKT4' in H16 as [].
      apply H12; auto. rewrite ImageSet_Property2. apply H7; auto.
    - destruct (classic (a ∈ f〈F∣B〉)); auto.
      assert (f⁻¹「a」 ⊂ A).
      { unfold Included; intros.
        apply AxiomII in H12 as [H12[]]. rewrite <-H1; auto. }
      apply H9 in H12 as []. elim H11. apply AxiomII; split; auto.
      apply (MKT33 B); auto. replace A with (f⁻¹「B」) in H12.
      rewrite <-ImageSet_Property4 in H12. right.
      assert ((B ~ a) ⊂ B).
      { unfold Included; intros. apply MKT4' in H13; tauto. }
      apply AxiomII; repeat split; auto. apply (MKT33 B); auto.
      apply AxiomI; split; intros. apply AxiomII in H13 as [H13[]].
      rewrite <-H1; auto. apply AxiomII. rewrite H1. repeat split; eauto.
      rewrite <-H1 in H13. apply Property_Value,Property_ran,H2
      in H13; auto. }
  apply AxiomII; split; auto. destruct H4. eauto with Fi.
Qed.

(* filter Theo5: transformation of principal ultrafilters *)
Theorem FT5_a : ∀ f A B a, Function f -> dom(f) = A -> ran(f) ⊂ B
  -> Ensemble A -> a ∈ A -> f〈(F A a)∣B〉 = F B f[a].
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H4 as [H4[]]. apply AxiomII in H6 as [H6[]].
    apply AxiomII in H8 as [H8[]]. apply AxiomII; auto.
  - apply AxiomII in H4 as [H4[]]. apply AxiomII; repeat split; auto.
    apply AxiomII. assert (f⁻¹「z」 ⊂ A).
    { unfold Included; intros. apply AxiomII in H7 as [H7[]].
      rewrite <-H0; auto. }
    repeat split; auto. apply MKT33 in H7; auto.
    apply AxiomII. rewrite H0. split; eauto.
Qed.

Theorem FT5_b : ∀ f A B a, Function f -> dom(f) = A -> ran(f) ⊂ B
  -> Ensemble A -> Ensemble B -> a ∈ A -> ultraFilter (f〈(F A a)∣B〉) B.
Proof.
  intros. rewrite FT5_a; auto. apply Fa_P2_b; auto.
  apply H1,(@ Property_ran a),Property_Value; auto. rewrite H0; auto.
Qed.

(* filter Theo6: each ultrafilter (even if not principal)
                 can be transformed to a principal ultrafilter,
                 by a constant function *)
Theorem FT6_a : ∀ F0 f A B b, F0 ∈ (β A) -> Function f
  -> dom(f) = A -> b ∈ B -> (∀ n, n ∈ A -> f[n] = b) -> f〈F0∣B〉 = F B b.
Proof.
  intros. assert (∀ B1, B1 ⊂ B -> f⁻¹「B1」 ∈ F0 <-> b ∈ B1).
  { split; intros.
    - apply NNPP; intro. assert (f⁻¹「B1」 = Φ).
      { apply AxiomI; split; intros. apply AxiomII in H7 as [H7[]].
        rewrite H1 in H8. apply H3 in H8. rewrite H8 in H9.
        contradiction. elim (@ MKT16 z); auto. }
      rewrite H7 in H5. apply AxiomII in H as [H[[H8[]]]].
      contradiction.
    - assert (f⁻¹「B1」 = A).
      { apply AxiomI; split; intros. apply AxiomII in H6 as [H6[]].
        rewrite H1 in H7; auto. apply AxiomII. rewrite H1.
        repeat split; eauto. apply H3 in H6. rewrite H6; auto. }
      rewrite H6. apply AxiomII in H as [H[[H7[H8[]]]]]; auto. }
  apply AxiomI; split; intros.
  - apply AxiomII in H5 as [H5[]]. pose proof H6 as H6'.
    apply H4 in H6. apply H6 in H7. apply AxiomII; auto.
  - apply AxiomII in H5 as [H5[]]. apply AxiomII; repeat split; auto.
    apply H4 in H6. apply H6; auto.
Qed.

Theorem FT6_b : ∀ F0 f A B b, F0 ∈ (β A) -> Function f
  -> dom(f) = A -> b ∈ B -> (∀ n, n ∈ A -> f[n] = b)
  -> Ensemble B -> ultraFilter (f〈F0∣B〉) B.
Proof.
  intros. rewrite (FT6_a F0 f A B b); auto. apply Fa_P2_b; auto.
Qed.

(* constand function *)
Definition Const A b := \{\ λ u v, u ∈ A /\ v = b \}\.

(* verify: (Const A b) is indeed the function (A → [b]  *)
Fact Const_is_Function : ∀ A b, A <> Φ -> Ensemble b
  -> Function (Const A b) /\ dom(Const A b) = A /\ ran(Const A b) = [b].
Proof.
  repeat split; intros.
  - unfold Relation; intros.
    apply AxiomII in H1 as [H1[x[y[]]]]; eauto.
  - apply AxiomII' in H1 as [H1[]]. apply AxiomII' in H2 as [H2[]].
    rewrite H4,H6; auto.
  - apply AxiomI; split; intros. apply AxiomII in H1 as [H1[]].
    apply AxiomII' in H2 as [H2[]]; auto. apply AxiomII; split;
    eauto. exists b. apply AxiomII'; split; auto. apply MKT49a; eauto.
  - apply AxiomI; split; intros. apply AxiomII in H1 as [H1[]].
    apply AxiomII' in H2 as [H2[]]. apply MKT41; eauto.
    apply AxiomII; split; eauto. apply NEexE in H as [a]. exists a.
    apply AxiomII'. apply MKT41 in H1; eauto. split; auto.
    rewrite H1. apply MKT49a; eauto.
Qed.

(* verify: ultrafilter can be transformed to the principal ultrafilter Fb
           by (Const A b)        *)
Property F_Const_Fa : ∀ F0 A B b, F0 ∈ (β A) -> b ∈ B
  -> (Const A b)〈F0∣B〉 = F B b.
Proof.
  intros. apply AxiomII in H as []. apply AxiomI; split; intros.
  - apply AxiomII in H2 as [H2[]]. apply AxiomII; repeat split;
    auto. apply NNPP; intro.
    assert ((Const A b)⁻¹「z」 = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H6 as [H6[]].
      pose proof H0. assert (Ensemble b); eauto.
      apply (Const_is_Function A b) in H10 as [H10[]].
      apply Property_Value,Property_ran in H7; auto.
      rewrite H12 in H7. apply MKT41 in H7; eauto. rewrite H7 in H8.
      contradiction. destruct H1 as [[_[H1[]]]]. intro.
      rewrite H14 in H11; auto. elim (@ MKT16 z0); auto. }
    rewrite H6 in H4. destruct H1 as [[H1[]]]; auto.
  - apply AxiomII in H2 as [H2[]]. apply AxiomII; repeat split; auto.
    assert ((Const A b)⁻¹「z」 = A).
    { apply AxiomI; split; intros. apply AxiomII in H5 as [H5[]].
      assert (Ensemble b); eauto. apply (Const_is_Function A b) in H8 as [H8[]].
      rewrite <-H9; auto. intro. destruct H1 as [[_[H1[]]]].
      rewrite H9 in H10; auto. apply AxiomII. assert (Ensemble b); eauto.
      apply (Const_is_Function A b) in H6 as [H6[]]. rewrite <-H7 in H5.
      repeat split; eauto. apply Property_Value,Property_ran
      in H5; auto. rewrite H8 in H5. apply MKT41 in H5; eauto. rewrite H5; auto.
      destruct H1 as [[_[H1[]]]]. intro. rewrite H10 in H7; auto. }
    destruct H1 as [[H1[H6[H7[]]]]]. rewrite H5; auto.
Qed.

(* filter Theo7: the f involved in FT6 is not naccessarilly a constant function,
                 it is only required to take a constant at
                 a certain element of the F0 involved in FT6 *)
Theorem FT7 : ∀ F0 f A B b, F0 ∈ (β A) -> Function f
  -> dom(f) = A -> ran(f) ⊂ B -> b ∈ B
  -> (∃ A1, A1 ∈ F0 /\ (∀ n, n ∈ A1 -> f[n] = b))
  -> f〈F0∣B〉 = F B b.
Proof.
  intros. destruct H4 as [a[]].
  apply AxiomII in H as [H[[H6[H7[H8[]]]]]].
  apply AxiomI; split; intros.
  - apply AxiomII in H12 as [H12[]].
    assert ((A ~ a) ∉ F0).
    { intro. assert (((A ~ a) ∩ a) ∈ F0). { apply H9; auto. }
      replace ((A ~ a) ∩ a) with Φ in H16; auto.
      apply AxiomI; split; intros. elim (@ MKT16 z0); auto.
      apply MKT4' in H17 as []. apply MKT4' in H17 as [].
      apply AxiomII in H19 as []. contradiction. }
    assert (~ f⁻¹「z」 ⊂ (A ~ a)).
    { intro. elim H15. apply (H10 f⁻¹「z」 _); auto.
      unfold Included; intros. apply MKT4' in H17; tauto. }
    apply AxiomII; repeat split; auto. apply NNPP; intro. elim H16.
    unfold Included; intros. apply AxiomII in H18 as [H18[]].
    rewrite H1 in H19. apply MKT4'; split; auto.
    apply AxiomII; split; auto. intro. apply H5 in H21.
    rewrite H21 in H20; auto.
  - apply AxiomII in H12 as [H12[]].
    assert (a ⊂ f⁻¹「z」).
    { unfold Included; intros. apply AxiomII; split. eauto.
      split. apply H6,AxiomII in H4 as []. apply H16 in H15.
      rewrite H1; auto. apply H5 in H15. rewrite H15; auto. }
    assert (f⁻¹「z」 ∈ F0).
    { apply (H10 a _); auto. unfold Included; intros.
      apply AxiomII in H16 as [H16[]]. rewrite H1 in H17; auto. }
    apply AxiomII; auto.
Qed.

(* Def: Function f and g are equal F0-almost everywhere;
         a.k.a. Function f and g are F0-equivalent:

         { u : u ∈ A /\ f(u) = g(u) } ∈ F0.

         where F0 is an UF over A, f and g are functions (A → B)  *)
Definition AlmostEqual f g A B F := Function f /\ Function g
  /\ dom(f) = A /\ dom(g) = A /\ ran(f) ⊂ B /\ ran(g) ⊂ B
  /\ F ∈ (β A) /\ \{ λ u, u ∈ A /\ f[u] = g[u] \} ∈ F.

(* filter Theo8: if function f and g are equal F0-almost everywhere,
                  then the transformation of F0 by f and g are equal. *)
Theorem FT8 : ∀ f g A B F0, AlmostEqual f g A B F0 -> f〈F0∣B〉 = g〈F0∣B〉.
Proof.
  intros. apply NNPP; intro. destruct H as [H[H1[H2[H3[H4[H5[]]]]]]].
  apply AxiomII in H6 as [H6[[H8[H9[H10[]]]]]].
  destruct (classic (f〈F0∣B〉 ⊂ g〈F0∣B〉)).
  - assert ((g〈F0∣B〉 ~ f〈F0∣B〉) <> Φ).
    { intro. elim H0. apply AxiomI; split; intros.
      apply H14; auto. apply NNPP; intro.
      assert (z ∈ Φ).
      { rewrite <-H15. apply MKT4'; split; auto.
        apply AxiomII; split; eauto. }
      pose proof (@ MKT16 z); auto. }
    apply NEexE in H15 as [b]. apply MKT4' in H15 as [].
    apply AxiomII in H16 as []. apply AxiomII in H15 as [H15[]].
    assert (f⁻¹「b」 ∉ F0).
    { intro. elim H17. apply AxiomII; split; auto. }
    assert (f⁻¹「b」 ⊂ A).
    { unfold Included; intros.
      apply AxiomII in H21 as [H21[]]. rewrite <-H2; auto. }
    apply H13 in H21 as []; auto. replace A with (f⁻¹「B」) in H21.
    rewrite <-ImageSet_Property4 in H21.
    assert ((g⁻¹「b」 ∩ f⁻¹「B ~ b」 ∩ \{ λ u, u ∈ A
      /\ f[u] = g[u] \}) ∈ F0). { apply H11; auto. }
    replace (g⁻¹「b」 ∩ f⁻¹「B ~ b」 ∩ \{ λ u, u ∈ A
      /\ f[u] = g[u] \}) with Φ in H22; auto.
    apply AxiomI; split; intros. elim (@ MKT16 z); auto.
    apply MKT4' in H23 as []. apply MKT4' in H24 as [].
    apply AxiomII in H23 as [H23[]]. apply AxiomII in H24 as [H24[]].
    apply AxiomII in H25 as [H25[]]. apply MKT4' in H29 as [].
    apply AxiomII in H32 as []. rewrite H31 in H33. contradiction.
    apply AxiomI; split; intros. apply AxiomII in H22 as [H22[]].
    rewrite <-H2; auto. apply AxiomII; split. eauto.
    rewrite <-H2 in H22. split; auto.
    apply Property_Value,Property_ran in H22; auto.
  - assert (∃ b, b ∈ f〈F0∣B〉 /\ b ∉ g〈F0∣B〉).
    { destruct (classic (f〈F0∣B〉 ~ g〈F0∣B〉 = Φ)).
      - elim H14. unfold Included; intros. apply NNPP; intro.
        assert (z ∈ (f〈F0∣B〉 ~ g〈F0∣B〉)).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto. }
        rewrite H15 in H18. pose proof (@ MKT16 z); auto.
      - apply NEexE in H15 as []. apply MKT4'
        in H15 as []. apply AxiomII in H16 as []; eauto. }
    destruct H15 as [b[]]. apply AxiomII in H15 as [H15[]].
    assert (g⁻¹「b」 ∉ F0).
    { intro. elim H16. apply AxiomII; split; auto. }
    assert (g⁻¹「b」 ⊂ A).
    { unfold Included; intros.
      apply AxiomII in H20 as [H20[]]. rewrite <-H3; auto. }
    apply H13 in H20 as []; auto. replace A with (g⁻¹「B」) in H20.
    rewrite <-ImageSet_Property4 in H20.
    assert ((f⁻¹「b」 ∩ g⁻¹「B ~ b」 ∩ \{ λ u, u ∈ A
      /\ f[u] = g[u] \}) ∈ F0). { apply H11; auto. }
    replace (f⁻¹「b」 ∩ g⁻¹「B ~ b」 ∩ \{ λ u, u ∈ A
      /\ f[u] = g[u] \}) with Φ in H21; auto.
    apply AxiomI; split; intros. elim (@ MKT16 z); auto.
    apply MKT4' in H22 as []. apply MKT4' in H23 as [].
    apply AxiomII in H22 as [H22[]]. apply AxiomII in H23 as [H23[]].
    apply AxiomII in H24 as [H24[]]. apply MKT4' in H28 as [].
    apply AxiomII in H31 as []. rewrite <-H30 in H32. contradiction.
    apply AxiomI; split; intros. apply AxiomII in H21 as [H21[]].
    rewrite <-H3; auto. apply AxiomII; split. eauto.
    rewrite <-H3 in H21. split; auto.
    apply Property_Value,Property_ran in H21; auto.
Qed.

(* Def: Arithmetical UltraFilter (AUF) over A (A is an infinite set).
         F0 is an AUF, that is to say,
         the equivalence of two transformation (by f and g) of F0
         implies that f and g are F0-equivalent, where f and g are A → A  *)
Definition Arithmetical_ultraFilter F A := ~ Finite A /\ F ∈ (β A)
  /\ (∀ f g, Function f -> Function g
    -> dom(f) = A -> dom(g) = A -> ran(f) ⊂ A -> ran(g) ⊂ A
    -> f〈F∣A〉 = g〈F∣A〉 -> AlmostEqual f g A A F).

(* corollary: f and g in the Def above can be A → B;
              namely, AUF meets the conversion of FT8   *)
Property AUF_Property : ∀ f g A B F0, Function f -> Function g
  -> dom(f) = A -> dom(g) = A -> ran(f) ⊂ B -> ran(g) ⊂ B
  -> Arithmetical_ultraFilter F0 A -> f〈F0∣B〉 = g〈F0∣B〉
  -> AlmostEqual f g A B F0.
Proof.
  intros. assert (Ensemble A /\ ~ Finite A /\ Ensemble F0) as [H7[]].
  { destruct H5 as [H5[]]. apply AxiomII in H7 as [H7[]]. split; eauto with Fi. }
  assert (Ensemble dom(f) /\ Ensemble dom(g)) as []. { rewrite H1,H2; auto. }
  assert (∃ h, Function1_1 h /\ dom(h) = ran(f) ∪ ran(g) /\ ran(h) ⊂ dom(f))
  as [h[[][]]]. { apply Inf_P9_and_P10_Corollary; auto; rewrite H1; auto. }
  assert (Ensemble dom(h)).
  { rewrite H14. apply AxiomIV; apply AxiomV; auto. }
  set (y1 := h ∘ f). set (y2 := h ∘ g).
  assert (Function y1 /\ Function y2) as []. { split; apply MKT64; auto. }
  assert (dom(y1) = A /\ dom(y2) = A) as [].
  { split; apply AxiomI; split; intros;
    try (apply AxiomII in H19 as [H19[]]; apply AxiomII' in H20 as [H20[x0[]]];
    apply Property_dom in H21); try (apply AxiomII; split; eauto).
    rewrite <-H1; auto. exists h[f[z]].
    assert ([z,f[z]] ∈ f). { apply Property_Value; auto. rewrite H1; auto. }
    assert ([f[z],h[f[z]]] ∈ h).
    { apply Property_Value; auto. apply Property_ran in H20. rewrite H14.
      apply MKT4; auto. } apply AxiomII'; split; eauto. apply MKT49a; eauto.
    assert (Ensemble ([f[z],h[f[z]]])). eauto. apply MKT49b in H22; tauto.
    rewrite <-H2; auto. exists h[g[z]].
    assert ([z,g[z]] ∈ g). { apply Property_Value; auto. rewrite H2; auto. }
    assert ([g[z],h[g[z]]] ∈ h).
    { apply Property_Value; auto. apply Property_ran in H20. rewrite H14.
      apply MKT4; auto. } apply AxiomII'; split; eauto. apply MKT49a; eauto.
    assert (Ensemble ([g[z],h[g[z]]])). eauto. apply MKT49b in H22; tauto. }
  assert (ran(y1) ⊂ A /\ ran(y2) ⊂ A) as [].
  { split; red; intros; apply AxiomII in H21 as [H21[]];
    apply AxiomII' in H22 as [H22[x0[]]]; apply Property_ran in H24;
    rewrite <-H1; auto. }
  assert (∀ a, h⁻¹「a」 ⊂ dom(h)).
  { red; intros. apply AxiomII in H23 as [_[]]; auto. }
  assert (∀ a, h⁻¹「a」 ⊂ B).
  { red; intros. apply H23 in H24. rewrite H14 in H24.
    apply MKT4 in H24 as []; auto. }
  assert (∀ a, y1⁻¹「a」 ∈ F0 <-> h⁻¹「a」 ∈ f〈F0∣B〉).
  { split; intros. apply AxiomII. rewrite <-ImageSet_Property10_b; auto.
    split; auto. apply (MKT33 dom(h)); auto. apply AxiomII in H25 as [H25[]].
    rewrite <-ImageSet_Property10_b in H27; auto. }
  assert (∀ a, y2⁻¹「a」 ∈ F0 <-> h⁻¹「a」 ∈ g〈F0∣B〉).
  { split; intros. apply AxiomII. rewrite <-ImageSet_Property10_b; auto.
    split; auto. apply (MKT33 dom(h)); auto. apply AxiomII in H26 as [H26[]].
    rewrite <-ImageSet_Property10_b in H28; auto. }
  assert (y1〈F0∣A〉 = y2〈F0∣A〉).
  { apply AxiomI; split; intros; apply AxiomII in H27 as [H27[]];
    apply AxiomII; repeat split; auto. apply H26. rewrite <-H6.
    apply H25; auto. apply H25. rewrite H6. apply H26; auto. }
  New H27. destruct H5. apply H29 in H28 as [_[_[_[_[_[_[]]]]]]]; auto.
  split; auto. split; auto. repeat split; auto.
  apply AxiomII in H28 as [_[[_[_[_[]]]]_]].
  apply (H31 \{ λ u, u ∈ A /\ y1[u] = y2[u] \}); auto; red; intros.
  apply AxiomII in H32 as [H32[]]. apply AxiomII; repeat split; auto.
  unfold y1,y2 in H34. rewrite ImageSet_Property10_Lemma,
  ImageSet_Property10_Lemma in H34; auto. apply f11inj in H34; auto;
  rewrite H14; apply MKT4; [left|right]; apply (@ Property_ran z);
  apply Property_Value; auto; [rewrite H1|rewrite H2]; auto.
  apply AxiomII in H32; tauto.
Qed.

(* filter Theo9: Every principal ultrafilter over an infinite set A is an AUF *)
Theorem FT9 : ∀ A a, Ensemble A -> ~ Finite A -> a ∈ A
  -> Arithmetical_ultraFilter (F A a) A.
Proof.
  intros. assert ((F A a) ∈ (β A)).
  { apply (Fa_P2_b A a) in H; [apply AxiomII; split; auto| ]; auto.
    destruct H; eauto with Fi. }
  split; auto. split; auto. split; auto. split; auto. repeat split; auto.
  rewrite FT5_a,FT5_a in H9; auto.
  assert (f[a] = g[a]).
  { apply NNPP; intro. apply (Example2 A) in H10; auto;
    [apply H7|apply H8]; apply (@ Property_ran a),Property_Value; auto;
    [rewrite H5|rewrite H6]; auto. }
  assert (\{ λ u, u ∈ A /\ f[u] = g[u] \} ⊂ A).
  { unfold Included; intros. apply AxiomII in H11 as []; tauto. }
  apply AxiomII; repeat split; auto. apply MKT33 with A; auto.
  apply AxiomII; split; eauto.
Qed.

(* transformation of ultrafilters by composite functions *)
Lemma FT10_Lemma : ∀ F0 A B f g, Function f -> Function g
  -> Ensemble A -> dom(g) ⊂ A -> g〈f〈F0∣A〉∣B〉 = (g ∘ f)〈F0∣B〉.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H3 as [H3[]]. apply AxiomII in H5 as [H5[]].
    apply AxiomII; repeat split; auto. rewrite ImageSet_Property10_b; auto.
  - apply AxiomII in H3 as [H4[]].
    apply AxiomII; repeat split; auto. apply AxiomII.
    assert (g⁻¹「z」 ⊂ A).
    { unfold Included; intros. apply AxiomII in H6 as [H6[]]; auto. }
    repeat split; auto. apply (MKT33 A); auto.
    rewrite <-ImageSet_Property10_b; auto.
Qed.

(* filter Theo10: AUF over A can be transformed to an AUF over B
                  by the function f (A → B)                       *)
Theorem FT10 : ∀ F0 f A B, Arithmetical_ultraFilter F0 A
  -> Function f -> dom(f) = A -> ran(f) ⊂ B -> Ensemble B -> ~ Finite B
  -> Arithmetical_ultraFilter (f〈F0∣B〉) B.
Proof.
  intros. assert (f〈F0∣B〉 ∈ (β B)) as H'.
  { apply (FT4 F0 f A B); auto. destruct H as [_[]]; auto. }
  split; auto. split; auto. intros h1 h2. intros.
  rewrite FT10_Lemma,FT10_Lemma in H11; auto; [ |rewrite H8|rewrite H7]; auto.
  assert (Function (h1 ∘ f) /\ Function (h2 ∘ f)) as [].
  { split; apply MKT64; auto. }
  assert (dom(h1 ∘ f) = A /\ dom(h2 ∘ f) = A) as [].
  { split; apply AxiomI; split; intros;
    try (apply AxiomII in H14 as [H14[]]; apply AxiomII' in H15 as [H15[x0[]]];
    apply Property_dom in H16); try (apply AxiomII; split; eauto).
    rewrite <-H1; auto. exists h1[f[z]].
    assert ([z,f[z]] ∈ f). { apply Property_Value; auto. rewrite H1; auto. }
    assert ([f[z],h1[f[z]]] ∈ h1).
    { apply Property_Value; auto. apply Property_ran in H15. rewrite H7; auto. }
    apply AxiomII'; split; eauto. apply MKT49a; eauto.
    assert (Ensemble ([f[z],h1[f[z]]])). eauto. apply MKT49b in H17; tauto.
    rewrite <-H1; auto. exists h2[f[z]].
    assert ([z,f[z]] ∈ f). { apply Property_Value; auto. rewrite H1; auto. }
    assert ([f[z],h2[f[z]]] ∈ h2).
    { apply Property_Value; auto. apply Property_ran in H15. rewrite H8; auto. }
    apply AxiomII'; split; eauto. apply MKT49a; eauto.
    assert (Ensemble ([f[z],h2[f[z]]])). eauto. apply MKT49b in H17; tauto. }
  assert (ran(h1 ∘ f) ⊂ B /\ ran(h2 ∘ f) ⊂ B) as [].
  { split; red; intros; apply AxiomII in H16 as [H16[]];
    apply AxiomII' in H17 as [H17[x0[]]]; apply Property_ran in H19; auto. }
  apply (AUF_Property _ _ A) in H11 as [_[_[_[_[_[_[_]]]]]]]; auto.
  split; auto. split; auto. repeat split; auto. apply AxiomII.
  assert (\{ λ u, u ∈ B /\ h1[u] = h2[u] \} ⊂ B).
  { red; intros. apply AxiomII in H18; tauto. }
  repeat split; auto. apply (MKT33 B); auto. destruct H as [_[]].
  apply AxiomII in H as [_[[_[_[_[]]]]_]].
  apply (H20 \{ λ u, u ∈ A /\ (h1 ∘ f)[u] = (h2 ∘ f)[u] \}); auto; red; intros;
  apply AxiomII in H21 as [H21[]]. apply AxiomII. split; auto. split.
  rewrite H1; auto. apply AxiomII. rewrite <-H1 in H22.
  apply Property_Value,Property_ran in H22; auto. repeat split; eauto.
  rewrite <-ImageSet_Property10_Lemma,<-ImageSet_Property10_Lemma; auto.
  rewrite <-H1; auto.
Qed.

