(*    This file presents the formalization for construction of *Z.   *)
(*  It is developmented in the CoqIDE (version 8.13.2) for windows.  *)

(** Ns_to_Zs *)

Require Export fmcr.construction_of_Ns.
Require Export mk.equivalence_relation.

(* 定义一个关系, 之后可以证明: 此关系为 *N × *N 上的等价关系. *)
Definition R_N' := \{\ λ u v, ∃ m n p q, m ∈ N' /\ n ∈ N' /\ p ∈ N' /\ q ∈ N'
  /\ u = [m,n] /\ v = [p,q] /\ m + q = n + p \}\.

(* 证明: 关系R_N' 为 *N × *N 上的等价关系.*)
Property R_N'_is_equRelation : equRelation R_N' (N' × N').
Proof.
  destruct NPAUF as [H' _]. repeat split; intros.
  - unfold Included; intros. apply AxiomII in H
    as [H[u[v[H0[m[n[p[q[H1[H2[H3[H4[H5[]]]]]]]]]]]]]].
    rewrite H0 in *. apply AxiomII'; split; auto.
    rewrite H5,H6. split; apply AxiomII'; split;
    try apply MKT49a; eauto.
  - unfold Reflexivity; intros. apply AxiomII in H
    as [H[m[n[H0[]]]]]. apply AxiomII; split.
    apply MKT49a; auto. exists [m,n],[m,n].
    rewrite H0. split; auto. exists m,n,m,n.
    repeat split; auto. apply N'_Plus_Commutation; auto.
  - unfold Symmetry; intros.
    apply AxiomII in H as [H[x0[y0[H2[]]]]].
    apply AxiomII in H0 as [H0[x1[y1[H5[]]]]]. rewrite H2,H5 in *.
    apply AxiomII' in H1
    as [H1[m[n[p[q[H8[H9[H10[H11[H12[]]]]]]]]]]].
    rewrite H12,H13 in *. apply AxiomII'; split.
    apply MKT49a; apply MKT49b in H1; tauto. exists p,q,m,n.
    repeat split; auto. rewrite N'_Plus_Commutation,
    (N'_Plus_Commutation q); auto.
  - unfold Transitivity; intros.
    apply AxiomII in H as [H[x0[y0[H4[]]]]].
    apply AxiomII in H0 as [H0[x1[y1[H7[]]]]].
    apply AxiomII in H1 as [H1[x2[y2[H10[]]]]].
    apply AxiomII' in H2
    as [H2[m0[n0[p0[q0[H13[H14[H15[H16[H17[]]]]]]]]]]].
    apply AxiomII' in H3
    as [H3[m1[n1[p1[q1[H20[H21[H22[H23[H24[]]]]]]]]]]].
    rewrite H4,H7,H10 in *. apply AxiomII'; split.
    apply MKT49a; auto. exists m0,n0,p1,q1. repeat split; auto.
    rewrite H18 in H24. apply MKT55 in H24 as []; eauto.
    rewrite H24,H27 in H19.
    assert ((m0 + n1) + (m1 + q1) = (n0 + m1) + (n1 + p1)).
    { rewrite H19,H26; auto. }
    rewrite (N'_Plus_Commutation m0) in H28; auto. rewrite
    N'_Plus_Association in H28; try apply N'_Plus_in_N'; auto.
    rewrite (N'_Plus_Commutation (n0 + m1)),(N'_Plus_Association n1),
    (N'_Plus_Commutation m0),(N'_Plus_Association m1),
    <-(N'_Plus_Association n1),(N'_Plus_Commutation n0),
    (N'_Plus_Commutation p1),<-(N'_Plus_Association n1),
    <-(N'_Plus_Association n1 _ _),(N'_Plus_Association _ _ p1),
    (N'_Plus_Commutation _ m0) in H28; try apply N'_Plus_in_N'; auto.
    apply N'_Plus_Cancellation in H28; try apply N'_Plus_in_N'; auto.
Qed.

Declare Scope z'_scope.
Delimit Scope z'_scope with z'.
Open Scope z'_scope.

Notation "\[ u \]" := (equClass u R_N' (N' × N'))(at level 5) : z'_scope.

(* 证明: [(m,n)] = [(p,q)] 即 m+q = n+p. *)
Property R_N'_Property : ∀ m n p q, m ∈ N' -> n ∈ N' -> p ∈ N' -> q ∈ N'
  -> \[[m,n]\] = \[[p,q]\] <-> m + q = n + p.
Proof.
  destruct NPAUF as [H _]. split; intros.
  - apply equClassT1 in H4; try apply R_N'_is_equRelation; auto.
    apply AxiomII' in H4
    as [H4[m0[n0[p0[q0[H5[H6[H7[H8[H9[]]]]]]]]]]].
    apply MKT55 in H9 as []; eauto. apply MKT55 in H10 as []; eauto.
    rewrite H9,H10,H12,H13; auto.
    apply AxiomII'; split; try apply MKT49a; eauto.
    apply AxiomII'; split; try apply MKT49a; eauto.
  - apply equClassT1; try apply R_N'_is_equRelation; auto;
    try apply AxiomII'; try split; try apply MKT49a;
    try apply MKT49a; eauto. exists p,q,m,n; repeat split; auto.
    rewrite N'_Plus_Commutation,(N'_Plus_Commutation q); auto.
Qed.

(* 定义: *Z 为 *N×*N 关于 R_N' 的商集. *)
Definition Z' := ((N' × N') / R_N')%eqr.

(* *Z是一个集 *)
Property Z'_is_Set : Ensemble Z'.
Proof.
  intros. apply (MKT33 pow(N' × N')).
  apply MKT38a,MKT74; apply N'_is_Set; auto.
  unfold Included; intros. apply AxiomII in H as [H0[x[]]].
  apply AxiomII; split; auto. rewrite H1.
  unfold Included; intros. apply AxiomII in H2; tauto.
Qed.

Property Z'_Instantiate1 : ∀ u, u ∈ Z'
  -> ∃ m n, m ∈ N' /\ n ∈ N' /\ u = \[[m,n]\].
Proof.
  intros. apply AxiomII in H as [H[x[]]]. apply AxiomII in H0
  as [H0[m[n[H2[]]]]]. rewrite H2 in H1. eauto.
Qed.

Property Z'_Instantiate2 : ∀ m n, m ∈ N' -> n ∈ N' -> \[[m,n]\] ∈ Z'.
Proof.
  intros. assert (Ensemble (\[[m,n]\])).
  { apply (MKT33 (N' × N')).
    apply MKT74; apply N'_is_Set. unfold Included; intros.
    apply AxiomII in H1; tauto. }
  apply AxiomII; split; auto. exists ([m,n]). split; auto.
  apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Ltac inZ' H m n := apply Z'_Instantiate1 in H as [m[n[?[]]]]; auto.

(* 定义一个新的类, 之后的证明可见, 此类实际为 *Z 中的'零元'. *)
Definition Z'0 := \{\ λ u v, u ∈ N' /\ v ∈ N' /\ u = v \}\.

(* 定义一个新的类, 之后的证明可见, 此类实际为 *Z 中上的'幺元'. *)
Definition Z'1 := \{\ λ u v, v ∈ N' /\ u = v + (F 1) \}\.

(* 性质: Z'0 = [0,0]代表的等价类. [注: 这里的 0 是指 *N 中的零元, 本质为 F Φ] *)
Property Z'0_Property : Z'0 = \[[(F 0),(F 0)]\].
Proof.
  assert ((F 0) ∈ N').
  { destruct MKT135. apply Fn_in_N' in H; auto. }
  apply AxiomI; split; intros.
  - apply AxiomII in H0 as [H0[u[v[H1[H2[]]]]]]. rewrite H1,H4 in *.
    apply AxiomII; repeat split; try apply AxiomII'; try split;
    try apply MKT49a; try apply MKT49a; eauto.
    exists v,v,(F 0),(F 0). repeat split; auto.
  - apply AxiomII in H0 as [H0[]].
    apply AxiomII in H1 as [H1[x[y[H3[]]]]]. rewrite H3 in *.
    apply AxiomII' in H2 as [H2[m[n[p[q[H6[H7[H8[H9[H10[]]]]]]]]]]].
    apply MKT55 in H11 as []; try split; eauto.
    rewrite <-H11,<-H13 in H12. rewrite <-H11 in H8.
    rewrite (N'_Plus_Commutation m),(N'_Plus_Commutation n) in H12; auto.
    apply N'_Plus_Cancellation in H12; auto.
    apply MKT55 in H10 as []; try apply MKT49; eauto.
    rewrite H10,H14,H12. apply AxiomII'; split; try apply MKT49a; eauto.
Qed.

(* 验证: Z'0 确实是*Z中的元素 *)
Property Z'0_in_Z' : Z'0 ∈ Z'.
Proof.
  pose proof in_ω_0. rewrite Z'0_Property; auto.
  apply Z'_Instantiate2; auto; apply Fn_in_N'; auto.
Qed.

Global Hint Resolve Z'0_in_Z' : Z'.

(* 性质: Z'1 = [1,0]代表的等价类. [注: 这里的1是指*N中的幺元, 本质为 F 1] *)
Property Z'1_Property : Z'1 = \[[(F 1),(F 0)]\].
Proof.
  assert ((F 0) ∈ N').
  { destruct MKT135. apply Fn_in_N' in H; eauto. }
  assert ((F 1) ∈ N') as H0a.
  { pose proof in_ω_1. apply Fn_in_N' in H0; auto. }
  apply AxiomI; split; intros.
  - apply AxiomII in H0 as [H0[u[v[H1[]]]]]. rewrite H1,H3 in *.
    apply AxiomII; repeat split; try apply AxiomII'; try repeat
    split; auto. apply N'_Plus_in_N'; auto. apply MKT49a; auto.
    apply MKT49a; eauto. exists (v + (F 1)),v,(F 1),(F Φ).
    repeat split; auto. apply N'_Plus_in_N'; auto.
    apply N'_Plus_Property; try apply N'_Plus_in_N'; auto.
  - apply AxiomII in H0 as [H0[]].
    apply AxiomII in H1 as [H1[x[y[H3[]]]]]. rewrite H3 in *.
    apply AxiomII' in H2 as [H2[m[n[p[q[H6[H7[H8[H9[H10[]]]]]]]]]]].
    apply MKT55 in H11 as []; try split; eauto.
    rewrite <-H11,<-H13 in H12. rewrite N'_Plus_Property in H12; auto.
    apply MKT55 in H10 as []; try apply MKT49; eauto.
    rewrite H10,H14,H12. apply AxiomII'; split; try apply MKT49a; eauto.
    rewrite <-H12; eauto.
Qed.

(* 验证: Z'1 确实是*Z中的元素 *)
Property Z'1_in_Z' : Z'1 ∈ Z'.
Proof.
  intros. pose proof in_ω_0. pose proof in_ω_1. rewrite Z'1_Property; auto.
  apply Z'_Instantiate2; apply Fn_in_N'; auto.
Qed.

(* 验证 Z'0 和 Z'1 二者不相等. *)
Property Z'0_isnot_Z'1 : Z'0 <> Z'1.
Proof.
  intros; intro. pose proof in_ω_0; pose proof in_ω_1.
  apply Fn_in_N' in H0,H1. assert ([(F 1),(F 0)] ∈ Z'0).
  { rewrite H. apply AxiomII'; repeat split; try apply MKT49a; eauto.
    rewrite N'_Plus_Commutation,N'_Plus_Property; try split; auto. }
  apply AxiomII' in H2 as [H2[H3[]]]. elim N'0_isnot_N'1; auto.
Qed.

Property Z'1_in_Z'_notZero : Z'1 ∈ (Z' ~ [Z'0]).
Proof.
  pose proof Z'1_in_Z'. apply MKT4'; split; auto. apply AxiomII; split; eauto.
  intro. apply MKT41 in H0. elim Z'0_isnot_Z'1; auto. pose proof Z'0_in_Z'; eauto.
Qed.

Global Hint Resolve  Z'1_in_Z'  Z'1_in_Z'_notZero  :  Z'.

(* 定义 Z'上的序(小于)关系  *Z上的u和v, u前于(小于)v 就是说, 所有 可以代表u的[m,n] 和
                   所有 可以代表v的[p,q] 都要满足:  m+q 前于(小于) n+p *)
Definition Z'_Ord := \{\ λ u v, ∀ m n p q, m ∈ N' -> n ∈ N' -> p ∈ N' -> q ∈ N'
  -> u = \[[m,n]\] -> v = \[[p,q]\] -> (m + q) < (n + p) \}\.

Notation "u < v" := ([u,v] ∈ Z'_Ord) : z'_scope.

(* 验证  *Z上序关系的定义的合理性: 所规定的序关系 与 表示元素的代表 无关.
        若 [m,n] = [m1,n1]   [p,q] = [p1,q1]  (指等价类相同)
        则  m+q  *N小于  n+p    就等价于    m1+q1  *N小于  n1+p1
        [注: 实际上就是要验证:  *Z上的序关系与等价类代表的选择无关. ] *)
Property Z'_Ord_reasonable : ∀ m n p q m1 n1 p1 q1,
  m ∈ N' -> n ∈ N' -> p ∈ N' -> q ∈ N'
  -> m1 ∈ N' -> n1 ∈ N' -> p1 ∈ N' -> q1 ∈ N'
  -> \[[m,n]\] = \[[m1,n1]\] -> \[[p,q]\] = \[[p1,q1]\]
  -> ((m + q) < (n + p) <-> (m1 + q1) < (n1 + p1))%n'.
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _]. intros. apply R_N'_Property in H8,H9; auto.
  assert ((m + q) + (n1 + p1) = (n + p) + (m1 + q1)).
  { rewrite N'_Plus_Association,N'_Plus_Association,<-(N'_Plus_Association q),
    <-(N'_Plus_Association p),(N'_Plus_Commutation q),(N'_Plus_Commutation p),
    N'_Plus_Association,N'_Plus_Association,<-(N'_Plus_Association m),
    <-(N'_Plus_Association n),H8,H9; try apply N'_Plus_in_N'; auto. }
  split; intros.
  - assert (((n + p) + (m1 + q1)) < ((n + p) + (n1 + p1))).
    { rewrite <-H10,N'_Plus_Commutation,(N'_Plus_Commutation (n + p));
      try apply N'_Plus_PrOrder; try apply N'_Plus_in_N'; auto. }
    apply N'_Plus_PrOrder in H12; try apply N'_Plus_in_N'; auto.
  - assert (((m + q) + (m1 + q1)) < ((n + p) + (m1 + q1))).
    { rewrite <-H10; try apply N'_Plus_PrOrder; try apply N'_Plus_in_N'; auto. }
    rewrite N'_Plus_Commutation,(N'_Plus_Commutation (n + p)) in H12;
    try apply N'_Plus_PrOrder in H12; try apply N'_Plus_in_N'; auto.
  Close Scope n'_scope.
Qed.

(* *Z上序关系的实例化描述: 
               [m,n]  *Z前于  [p,q]   (指等价类前于)
        就是指   m+q   *N前于   n+p    (m n p q 都是*N中的元)   *)
Property Z'_Ord_Instantiate : ∀ m n p q, m ∈ N' -> n ∈ N' -> p ∈ N' -> q ∈ N'
  -> \[[m,n]\] < \[[p,q]\] <-> ((m + q) < (n + p))%n'.
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _]. split; intros.
  - apply AxiomII' in H4 as []. apply H5; auto.
  - apply AxiomII'; split. apply MKT49a; apply (MKT33 (N' × N'));
    try apply MKT74; try split; try apply N'_is_Set; destruct H; auto;
    unfold Included; intros; apply AxiomII in H6; tauto. intros.
    apply R_N'_Property in H9,H10; auto.
    assert (((n + m0) + ((p + q0) + (m + q)))
      < ((m + n0) + ((q + p0) + (n + p)))).
    { rewrite H9,H10.
      apply N'_Plus_PrOrder; try apply N'_Plus_in_N';
      try apply N'_Plus_in_N'; auto.
      apply N'_Plus_PrOrder; try apply N'_Plus_in_N';
      try apply N'_Plus_in_N'; auto. }
    rewrite (N'_Plus_Commutation n),
    (N'_Plus_Commutation m n0),(N'_Plus_Commutation p),
    (N'_Plus_Commutation q),N'_Plus_Association,
    (N'_Plus_Association n0),<-(N'_Plus_Association n),
    <-(N'_Plus_Association n),<-(N'_Plus_Association m),
    <-(N'_Plus_Association m),(N'_Plus_Commutation n q0),
    (N'_Plus_Commutation m p0),(N'_Plus_Association q0),
    (N'_Plus_Association q0),<-(N'_Plus_Association m0),
    (N'_Plus_Association p0),(N'_Plus_Association p0),
    <-(N'_Plus_Association n0),
    (N'_Plus_Commutation (n0 + p0)),
    N'_Plus_Commutation,(N'_Plus_Commutation n p),
    (N'_Plus_Commutation (p + n)) in H11;
    try apply N'_Plus_in_N'; try apply N'_Plus_in_N'; auto.
    apply N'_Plus_PrOrder in H11; try apply N'_Plus_in_N';
    try apply N'_Plus_in_N'; auto.
  Close Scope n'_scope.
Qed.

Property Z'0_lt_Z'1 : Z'0 < Z'1.
Proof.
  intros.
  assert (Z'0 ∈ Z' /\ Z'1 ∈ Z') as [].
  { split. apply Z'0_in_Z'; auto. apply Z'1_in_Z'; auto. }
  rewrite Z'0_Property,Z'1_Property; auto.
  pose proof in_ω_0; pose proof in_ω_1. apply Fn_in_N' in H1,H2.
  apply Z'_Ord_Instantiate; auto.
  rewrite N'_Plus_Property,N'_Plus_Commutation,N'_Plus_Property;
  auto. apply N'0_lt_N'1; auto.
Qed.

Global Hint Resolve Z'0_lt_Z'1 : Z'.

(* *Z上定义的 Z'_Ord关系 具有反自反性. *)
Property Z'_Ord_irReflex : ∀ u v, u ∈ Z' -> v ∈ Z' -> u = v -> ~ u < v.
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _].
  intros. apply AxiomII in H0 as [H0[x[]]].
  apply AxiomII in H3 as [H3[m[n[H5[]]]]].
  apply AxiomII in H1 as [H1[y[]]].
  apply AxiomII in H8 as [H8[p[q[H10[]]]]].
  rewrite H4,H9,H5,H10 in *. apply R_N'_Property in H2; auto.
  intro. apply Z'_Ord_Instantiate in H13; auto. rewrite H2 in H13.
  elim (N'_Ord_irReflex_weak (n + p)); try apply N'_Plus_in_N'; auto.
  Close Scope n'_scope.
Qed.

(* *Z上定义的 Z'_Ord关系 具有可传递性.  *)
Property Z'_Ord_Trans : ∀ u v w, u ∈ Z' -> v ∈ Z' -> w ∈ Z'
  -> u < v -> v < w -> u < w.
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[x[]]].
  apply AxiomII in H5 as [H5[m[n[H7[]]]]].
  apply AxiomII in H1 as [H1[y[]]].
  apply AxiomII in H10 as [H10[p[q[H12[]]]]].
  apply AxiomII in H2 as [H2[z[]]].
  apply AxiomII in H15 as [H15[j[k[H17[]]]]].
  rewrite H6,H11,H16,H7,H12,H17 in *.
  apply Z'_Ord_Instantiate in H3; auto.
  apply Z'_Ord_Instantiate in H4; auto. apply Z'_Ord_Instantiate; auto.
  assert (∀ a b c d, a ∈ N' -> b ∈ N' -> c ∈ N' -> d ∈ N' -> a < b -> c < d
    -> (a + c) < (b + d)).
  { intros. assert ((a + d) < (b + d)).
    { rewrite N'_Plus_Commutation,(N'_Plus_Commutation b); auto.
      apply N'_Plus_PrOrder; auto. }
    assert ((a + c) < (a + d)). { apply N'_Plus_PrOrder; auto. }
    apply (N'_Ord_Trans _ (a + d));
    try apply N'_Plus_in_N'; auto; destruct H; auto. }
  apply (H20 (m + q) (n + p)) in H4; try apply N'_Plus_in_N'; auto. clear H20.
  rewrite N'_Plus_Association,N'_Plus_Association,<-(N'_Plus_Association q),
  <-(N'_Plus_Association p),(N'_Plus_Commutation q),<-(N'_Plus_Association m),
  <-(N'_Plus_Association n),(N'_Plus_Commutation m),(N'_Plus_Commutation n),
  (N'_Plus_Association _ _ k),(N'_Plus_Association _ _ j) in H4;
  try apply N'_Plus_in_N'; auto.
  apply N'_Plus_PrOrder in H4; try apply N'_Plus_in_N'; auto.
  Close Scope n'_scope.
Qed.

(* *Z上定义的 Z'_Ord关系 满足三分律, 也就是 Z'_Ord连接*Z.  *)
Property Z'_Ord_Tri : Connect Z'_Ord Z'.
Proof.
  Open Scope n'_scope.
  intros. unfold Connect; intros. apply AxiomII in H as [H[x[]]].
  apply AxiomII in H1 as [H1[m[n[H3[]]]]]. apply AxiomII in H0 as [H0[y[]]].
  apply AxiomII in H6 as [H6[p[q[H8[]]]]]. rewrite H2,H7,H3,H8 in *.
  assert ((m + q) ∈ N' /\ (n + p) ∈ N') as [].
  { split; apply N'_Plus_in_N'; auto. }
  apply (N'_Ord_Tri _ (n + p)) in H11; auto; clear H12.
  destruct H11 as [H11|[|]]; [left|right; left|right; right];
  try apply Z'_Ord_Instantiate; try apply R_N'_Property; auto.
  rewrite N'_Plus_Commutation,(N'_Plus_Commutation q); auto.
  Close Scope n'_scope.
Qed.

(* 定义: *Z上的加法, u + v 就是说   任意一个和u相等的等价类[(m,n)]
                              和 任意一个和v相等的等价类[(p,q)] 做运算,
                        运算结果为等价类[(m+p),(n+q)].   *)
Definition Z'_Plus u v := ∩(\{ λ a, ∀ m n p q, m ∈ N' -> n ∈ N'
  -> p ∈ N' -> q ∈ N' -> u = \[[m,n]\] -> v = \[[p,q]\]
  -> a = \[[(m + p)%n',(n + q)%n']\] \}).

Notation "u + v" := (Z'_Plus u v) : z'_scope.

(* 验证 *Z中定义的加法运算的合理性: 对于任意*Z中的u和v, *Z上的加法定义中的{}中只有
                               一个元素, 并且该唯一的元素也在*Z中, 于是u与v的
                               相加结果形如 ∩[a] 是属于*Z且唯一的.       *)
Property Z'_Plus_Reasonable : ∀ u v, u ∈ Z' -> v ∈ Z' -> ∃ a, a ∈ Z'
  /\ [a] = \{ λ a, ∀ m n p q, m ∈ N' -> n ∈ N' -> p ∈ N' -> q ∈ N'
    -> u = \[[m,n]\] -> v = \[[p,q]\] -> a = \[[(m + p)%n',(n + q)%n']\] \}.
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[x[]]].
  apply AxiomII in H1 as [H1[y[]]]. apply AxiomII in H2 as [H2[x0[y0[H6[]]]]].
  apply AxiomII in H4 as [H4[x1[y1[H9[]]]]].
  rewrite H6,H9 in *. exists (\[[(x0 + x1),(y0 + y1)]\]).
  assert (\[[(x0 + x1),(y0 + y1)]\] ∈ Z').
  { apply Z'_Instantiate2; try apply N'_Plus_in_N'; auto. }
  split; auto. apply AxiomI; split; intros.
  - apply MKT41 in H13; eauto. apply AxiomII; split.
    rewrite H13; eauto. intros. rewrite H13.
    apply R_N'_Property; try apply N'_Plus_in_N'; auto.
    rewrite H3 in H18. rewrite H5 in H19.
    apply R_N'_Property in H18; auto.
    apply R_N'_Property in H19; auto.
    rewrite N'_Plus_Association,<-(N'_Plus_Association x1),
    (N'_Plus_Commutation x1),N'_Plus_Association,
    <-N'_Plus_Association,(N'_Plus_Association y0),
    <-(N'_Plus_Association y1),(N'_Plus_Commutation y1),
    (N'_Plus_Association _ _ p),<-(N'_Plus_Association y0);
    try apply N'_Plus_in_N'; auto. rewrite H18,H19; auto.
  - apply AxiomII in H13 as []. apply MKT41; eauto.
  Close Scope n'_scope.
Qed.

Property Z'_Plus_Instantiate : ∀ m n p q, m ∈ N' -> n ∈ N' -> p ∈ N' -> q ∈ N'
  -> \[[m,n]\] + \[[p,q]\] = \[[(m + p)%n',(n + q)%n']\].
Proof.
  intros.
  assert (\[[m,n]\] ∈ Z'). { apply Z'_Instantiate2; auto. }
  assert (\[[p,q]\] ∈ Z'). { apply Z'_Instantiate2; auto. }
  pose proof H3. apply (Z'_Plus_Reasonable (\[[m,n]\]) (\[[p,q]\])) in H5
  as [a[]]; auto. unfold Z'_Plus. rewrite <-H6. apply AxiomII in H5 as [H5[x[]]].
  apply AxiomII in H7 as [H7[x0[y0[H9[]]]]]. rewrite H9 in H8.
  assert (a ∈ [a]). { apply MKT41; auto. }
  rewrite H6 in H12. clear H6. apply AxiomII in H12 as [].
  apply (H12 m n p q) in H; auto. rewrite <-H. apply MKT44; auto.
Qed.

(* 进一步验证 *Z上定义的加法对*Z封闭 *)
Property Z'_Plus_in_Z' : ∀ u v, u ∈ Z' -> v ∈ Z' -> (u + v) ∈ Z'.
Proof.
  intros. pose proof H. apply (Z'_Plus_Reasonable u v) in H1 as [a[]]; auto.
  assert (a ∈ [a]). { apply MKT41; eauto. }
  rewrite H2 in H3. clear H2. apply AxiomII in H3 as [].
  apply AxiomII in H as [H[x[]]]. apply AxiomII in H0 as [H0[y[]]].
  apply AxiomII in H4 as [H4[x0[y0[H8[]]]]].
  apply AxiomII in H6 as [H6[x1[y1[H11[]]]]].
  rewrite H8,H11 in *. pose proof H5. apply (H3 x0 y0 x1 y1) in H14; auto.
  rewrite H5,H7,Z'_Plus_Instantiate; auto. rewrite <-H14; auto.
Qed.

Global Hint Resolve Z'_Plus_in_Z' : Z'.

(* 定义: *Z上的乘法, u * v 就是说   任意一个和u相等的等价类[(m,n)]
                             和 任意一个和v相等的等价类[(p,q)] 做运算,
                        运算结果为等价类[(m*p + n*q),(m*q + n*p)].   *)
Definition Z'_Mult u v := ∩(\{ λ a, ∀ m n p q, m ∈ N' -> n ∈ N'
  -> p ∈ N' -> q ∈ N' -> u = \[[m,n]\] -> v = \[[p,q]\]
  -> a = \[[((m · p) + (n · q))%n', ((m · q) + (n · p))%n']\] \}).

Notation "u · v" := (Z'_Mult u v) : z'_scope.

(* 验证 *Z中定义的乘法运算的合理性: 对于任意*Z中的u和v, *Z上的加法定义中的{}中只有
                              一个元素, 并且该唯一的元素也在*Z中, 于是u与v的
                              相乘结果形如 ∩[a] 是属于*Z且唯一的.        *)
Property Z'_Mult_Reasonable : ∀ u v, u ∈ Z' -> v ∈ Z' -> ∃ a, a ∈ Z'
  /\ [a] = \{ λ a, ∀ m n p q, m ∈ N' -> n ∈ N' -> p ∈ N' -> q ∈ N'
    -> u = \[[m,n]\] -> v = \[[p,q]\]
    -> a = \[[((m · p) + (n · q))%n', ((m · q) + (n · p))%n']\] \}.
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[x[]]].
  apply AxiomII in H1 as [H1[y[]]]. apply AxiomII in H2 as [H2[x0[y0[H6[]]]]].
  apply AxiomII in H4 as [H4[x1[y1[H9[]]]]]. rewrite H6,H9 in *.
  set (A := \[[((x0 · x1) + (y0 · y1)), ((x0 · y1) + (y0 · x1))]\]).
  assert (Ensemble ([((x0 · x1) + (y0 · y1)), (x0 · y1) + (y0 · x1)])) as Ha.
  { pose proof H7; pose proof H8. apply MKT49a;
    apply (N'_Mult_in_N' x0 x1) in H7;
    apply (N'_Mult_in_N' y0 y1) in H8;
    apply (N'_Mult_in_N' x0 y1) in H12;
    apply (N'_Mult_in_N' y0 x1) in H13; eauto.
    apply (N'_Plus_in_N' _ (y0 · y1)) in H7; eauto.
    apply (N'_Plus_in_N' _ (y0 · x1)) in H12; eauto. }
  exists A. assert (A ∈ Z').
  { assert (A ⊂ N'×N').
    { unfold Included; intros. apply AxiomII in H12; tauto. }
    apply AxiomII; split. apply (MKT33 N'×N'); auto.
    apply MKT74; apply N'_is_Set; destruct H; auto.
    exists ([((x0 · x1) + (y0 · y1)),
    ((x0 · y1) + (y0 · x1))]). split; auto.
    apply AxiomII'; repeat split; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; auto. }
  split; auto. apply AxiomI; split; intros.
  - apply MKT41 in H13; eauto. apply AxiomII; split.
    rewrite H13; eauto. intros. rewrite H13.
    apply R_N'_Property; try apply N'_Plus_in_N'; try apply
    N'_Mult_in_N'; auto. rewrite H3 in H18. rewrite H5 in H19.
    apply R_N'_Property in H18; auto.
    apply R_N'_Property in H19; auto.
    assert (((x1 · (x0 + n)) + (y1 · (y0 + m))) + ((m · (x1 + q)) + (n · (y1 + p)))
      = ((x1 · (y0 + m)) + (y1 · (x0 + n))) + ((m · (y1 + p)) + (n · (x1 + q)))).
    { rewrite H18,H19; auto. }
    rewrite N'_Mult_Distribution,N'_Mult_Distribution,
    N'_Mult_Distribution,N'_Mult_Distribution,
    N'_Mult_Distribution,N'_Mult_Distribution,
    N'_Mult_Distribution,N'_Mult_Distribution in H20; auto.
    assert ((((x1 · x0) + (x1 · n)) + ((y1 · y0) + (y1 · m)))
      = (((x1 · x0) + (y1 · y0)) + ((x1 · n) + (y1 · m)))).
    { rewrite N'_Plus_Association,<-(N'_Plus_Association
      (x1 · n)),(N'_Plus_Commutation (x1 · n)),
      N'_Plus_Association,<-(N'_Plus_Association (x1 · x0));
      try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto. }
    assert ((((m · x1) + (m · q)) + ((n · y1) + (n · p)))
      = (((m · q) + (n · p)) + ((m · x1) + (n · y1)))).
    { rewrite (N'_Plus_Commutation (m · x1)),
      (N'_Plus_Commutation (n · y1)),N'_Plus_Association,
       <-(N'_Plus_Association (m · x1)),
      (N'_Plus_Commutation (m · x1)),N'_Plus_Association,
       <-(N'_Plus_Association (m · q));
      try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto. }
    assert ((((x1 · y0) + (x1 · m)) + ((y1 · x0) + (y1 · n)))
      = (((x1 · y0) + (y1 · x0)) + ((x1 · m) + (y1 · n)))).
    { rewrite N'_Plus_Association,
      <-(N'_Plus_Association (x1 · m)),
      (N'_Plus_Commutation (x1 · m)),N'_Plus_Association,
      <-(N'_Plus_Association (x1 · y0));
      try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto. }
    assert ((((m · y1) + (m · p)) + ((n · x1) + (n · q)))
      = (((m · p) + (n · q)) + ((m · y1) + (n · x1)))).
    { rewrite (N'_Plus_Commutation (m · y1)),
      (N'_Plus_Commutation (n · x1)),N'_Plus_Association,
      <-(N'_Plus_Association (m · y1)),
      (N'_Plus_Commutation (m · y1)),N'_Plus_Association,
      <-(N'_Plus_Association (m · p));
      try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto. }
    rewrite H21,H22,H23,H24 in H20. clear H21 H22 H23 H24.
    rewrite N'_Plus_Association,
    (N'_Plus_Association ((x1 · y0) + (y1 · x0))),
    <-(N'_Plus_Association ((x1 · n) + (y1 · m))),
    <-(N'_Plus_Association ((x1 · m) + (y1 · n))),
    (N'_Plus_Commutation ((x1 · n) + (y1 · m))),
    (N'_Plus_Commutation ((x1 · m) + (y1 · n))),
    (N'_Plus_Association ((m · q) + (n · p))),
    (N'_Plus_Association ((m · p) + (n · q))),
    <-(N'_Plus_Association ((x1 · x0) + (y1 · y0))),
    <-(N'_Plus_Association ((x1 · y0) + (y1 · x0))),
    N'_Plus_Commutation,
    (N'_Plus_Commutation (((x1 · y0) + (y1 · x0))
      + ((m · p) + (n · q)))) in H20;
    try apply N'_Plus_in_N'; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; auto.
    assert ((((x1 · n) + (y1 · m)) + ((m · x1) + (n · y1)))
      = (((x1 · m) + (y1 · n)) + ((m · y1) + (n · x1)))).
    { rewrite N'_Plus_Commutation,
      (N'_Plus_Commutation (x1 · n)),
      (N'_Mult_Commutation m),(N'_Mult_Commutation n),
      (N'_Mult_Commutation y1 m),(N'_Mult_Commutation x1 n);
       try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto. }
    rewrite H21 in H20. clear H21.
    apply N'_Plus_Cancellation in H20; try apply N'_Plus_in_N';
    try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
    rewrite (N'_Mult_Commutation x0),(N'_Mult_Commutation y0),
    (N'_Mult_Commutation x0),(N'_Mult_Commutation y0),
    (N'_Plus_Commutation (y1 · x0));
    try apply N'_Mult_in_N'; auto.
  - apply AxiomII in H13 as []. apply MKT41; eauto.
  Close Scope n'_scope.
Qed.

Property Z'_Mult_Instantiate : ∀ m n p q, m ∈ N' -> n ∈ N' -> p ∈ N' -> q ∈ N'
  -> \[[m,n]\] · \[[p,q]\] = \[[((m · p) + (n · q))%n', ((m · q) + (n · p))%n']\].
Proof.
  intros. assert (\[[m,n]\] ∈ Z'). { apply Z'_Instantiate2; auto. }
  assert (\[[p,q]\] ∈ Z'). { apply Z'_Instantiate2; auto. } pose proof H3.
  apply (Z'_Mult_Reasonable (\[[m,n]\]) (\[[p,q]\])) in H5 as [a[]]; auto.
  unfold Z'_Mult. rewrite <-H6. apply AxiomII in H5 as [H5[x[]]].
  apply AxiomII in H7 as [H7[x0[y0[H9[]]]]]. rewrite H9 in H8.
  assert (a ∈ [a]). { apply MKT41; auto. }
  rewrite H6 in H12. clear H6. apply AxiomII in H12 as [].
  apply (H12 m n p q) in H; auto. rewrite <-H. apply MKT44; auto.
Qed.

(* 进一步验证 *Z上定义的乘法对*Z封闭 *)
Property Z'_Mult_in_Z' : ∀ u v, u ∈ Z' -> v ∈ Z' -> (u · v) ∈ Z'.
Proof.
  intros. pose proof H. apply (Z'_Mult_Reasonable u v) in H1 as [a[]]; auto.
  assert (a ∈ [a]). { apply MKT41; eauto. }
  rewrite H2 in H3. clear H2. apply AxiomII in H3 as [].
  apply AxiomII in H as [H[x[]]]. apply AxiomII in H0 as [H0[y[]]].
  apply AxiomII in H4 as [H4[x0[y0[H8[]]]]], H6 as [H6[x1[y1[H11[]]]]].
  rewrite H8,H11 in *. pose proof H5. apply (H3 x0 y0 x1 y1) in H14; auto.
  rewrite H5,H7,Z'_Mult_Instantiate; auto. rewrite <-H14; auto.
Qed.

Global Hint Resolve Z'_Mult_in_Z' : Z'.

(* 验证 *Z中的关于零元性质: u + Z'0 = u  *)
Property Z'_Plus_Property : ∀ u, u ∈ Z' -> u + Z'0 = u.
Proof.
  intros. apply AxiomII in H as [H[x[]]].
  apply AxiomII in H0 as [H0[x0[y0[H2[]]]]].
  rewrite H2 in *. clear dependent x. destruct MKT135.
  apply Fn_in_N' in H2. rewrite H1,Z'0_Property,Z'_Plus_Instantiate; auto.
  apply R_N'_Property; try apply N'_Plus_in_N'; auto.
  rewrite N'_Plus_Property,N'_Plus_Property,N'_Plus_Commutation; auto.
Qed.

(* 验证 *Z中的加法满足交换律. *)
Property Z'_Plus_Commutation : ∀ u v, u ∈ Z' -> v ∈ Z' -> u + v = v + u.
Proof.
  Open Scope n'_scope.
  intros. apply AxiomII in H as [H[x[]]].
  apply AxiomII in H1 as [H1[x0[y0[H3[]]]]]. apply AxiomII in H0 as [H0[y[]]].
  apply AxiomII in H6 as [H6[x1[y1[H8[]]]]]. rewrite H3,H8 in *. rewrite H2,H7.
  rewrite Z'_Plus_Instantiate,Z'_Plus_Instantiate; auto.
  assert (x0 + x1 = x1 + x0). { apply N'_Plus_Commutation; auto. }
  assert (y0 + y1 = y1 + y0). { apply N'_Plus_Commutation; auto. }
  rewrite H11,H12; auto.
  Close Scope n'_scope.
Qed.

(* 验证 *Z中的加法满足结合律 *)
Property Z'_Plus_Association : ∀ u v w, u ∈ Z' -> v ∈ Z' -> w ∈ Z'
  -> (u + v) + w = u + (v + w).
Proof.
  Open Scope n'_scope.
  intros. apply AxiomII in H as [H[a[]]].
  apply AxiomII in H2 as [H2[x0[y0[H4[]]]]]. apply AxiomII in H0 as [H0[b[]]].
  apply AxiomII in H7 as [H7[x1[y1[H9[]]]]]. apply AxiomII in H1 as [H1[c[]]].
  apply AxiomII in H12 as [H12[x2[y2[H14[]]]]]. rewrite H3,H8,H13 in *.
  rewrite H4,H9,H14,Z'_Plus_Instantiate,Z'_Plus_Instantiate,Z'_Plus_Instantiate,
  Z'_Plus_Instantiate; try apply N'_Plus_in_N'; auto.
  assert ((x0 + x1) + x2 = x0 + (x1 + x2)). { apply N'_Plus_Association; auto. }
  assert ((y0 + y1) + y2 = y0 + (y1 + y2)). { apply N'_Plus_Association; auto. }
  rewrite H17,H18; auto.
  Close Scope n'_scope.
Qed.

(* 验证 *Z中的加法满足消去律 *)
Property Z'_Plus_Cancellation : ∀ u v w, u ∈ Z' -> v ∈ Z' -> w ∈ Z'
  -> u + v = u + w -> v = w.
Proof.
  intros. apply AxiomII in H as [H[a[]]].
  apply AxiomII in H3 as [H3[x0[y0[H5[]]]]]. apply AxiomII in H0 as [H0[b[]]].
  apply AxiomII in H8 as [H8[x1[y1[H10[]]]]]. apply AxiomII in H1 as [H1[c[]]].
  apply AxiomII in H13 as [H13[x2[y2[H15[]]]]]. rewrite H4,H9,H14 in *.
  rewrite H5,H10,H15 in *. rewrite Z'_Plus_Instantiate,Z'_Plus_Instantiate in H2;
  auto. apply R_N'_Property in H2; try apply N'_Plus_in_N'; auto.
  apply R_N'_Property; auto. rewrite N'_Plus_Association,N'_Plus_Association,
  <-(N'_Plus_Association x1),<-(N'_Plus_Association y1),(N'_Plus_Commutation x1),
  (N'_Plus_Commutation y1),N'_Plus_Association,N'_Plus_Association,
  <-(N'_Plus_Association x0),<-(N'_Plus_Association y0),
  (N'_Plus_Commutation x0) in H2; try apply N'_Plus_in_N'; auto.
  apply N'_Plus_Cancellation in H2; try apply N'_Plus_in_N'; auto.
Qed.


(* *Z上定义的 Z'_Ord关系 满足加法保序 (需注意和 消去律 的区别).  *)
Property Z'_Plus_PrOrder : ∀ u v w, u ∈ Z' -> v ∈ Z' -> w ∈ Z'
  -> u < v <-> (w + u) < (w + v).
Proof.
  destruct NPAUF as [H _].
  intros. apply AxiomII in H0 as [H0[x[]]].
  apply AxiomII in H3 as [H3[m[n[H5[]]]]].
  apply AxiomII in H1 as [H1[y[]]].
  apply AxiomII in H8 as [H8[p[q[H10[]]]]].
  apply AxiomII in H2 as [H2[z[]]].
  apply AxiomII in H13 as [H13[j[k[H15[]]]]].
  rewrite H4,H9,H14,H5,H10,H15 in *. split; intros.
  - apply Z'_Ord_Instantiate in H18; auto.
    rewrite Z'_Plus_Instantiate,Z'_Plus_Instantiate; auto.
    apply Z'_Ord_Instantiate; auto; try apply N'_Plus_in_N'; auto.
    rewrite N'_Plus_Association,N'_Plus_Association,
    <-(N'_Plus_Association m),<-(N'_Plus_Association n),
    (N'_Plus_Commutation m),(N'_Plus_Commutation n),
    N'_Plus_Association,N'_Plus_Association,
    <-(N'_Plus_Association j),<-(N'_Plus_Association k),
    (N'_Plus_Commutation j); try apply N'_Plus_in_N'; auto.
    apply N'_Plus_PrOrder; try apply N'_Plus_in_N'; auto.
  - apply Z'_Ord_Instantiate; auto.
    rewrite Z'_Plus_Instantiate,Z'_Plus_Instantiate in H18; auto.
    apply Z'_Ord_Instantiate in H18; auto;
    try apply N'_Plus_in_N'; auto.
    rewrite N'_Plus_Association,N'_Plus_Association,
    <-(N'_Plus_Association m),<-(N'_Plus_Association n),
    (N'_Plus_Commutation m),(N'_Plus_Commutation n),
    N'_Plus_Association,N'_Plus_Association,
    <-(N'_Plus_Association j),<-(N'_Plus_Association k),
    (N'_Plus_Commutation j) in H18;
    try apply N'_Plus_in_N'; auto.
    apply N'_Plus_PrOrder in H18; try apply N'_Plus_in_N'; auto.
Qed.

Corollary Z'_Plus_PrOrder_Corollary : ∀ u v, u ∈ Z' -> v ∈ Z'
  -> u < v <-> ∃! w, w ∈ Z' /\ Z'0 < w /\ u + w = v.
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _].
  intros. apply AxiomII in H0 as [H0[x[]]].
  apply AxiomII in H2 as [H2[m[n[H4[]]]]].
  apply AxiomII in H1 as [H1[y[]]].
  apply AxiomII in H7 as [H7[p[q[H9[]]]]].
  rewrite H4,H3,H9,H8 in *. split; intros.
  - apply Z'_Ord_Instantiate in H12; auto.
    apply N'_Plus_PrOrder_Corollary in H12 as [a[[H12[]]]];
    try apply N'_Plus_in_N'; auto.
    exists \[[a,(F 0)]\].
    pose proof H; pose proof in_ω_0. apply Fn_in_N' in H17. repeat split.
    + apply AxiomII; split. apply (MKT33 N'×N').
      apply MKT74; apply N'_is_Set; destruct H as [_[]]; auto.
      unfold Included; intros. apply AxiomII in H18; tauto.
      exists ([a,F 0]). split; auto.
      apply AxiomII'; split; try apply MKT49a; eauto.
    + rewrite Z'0_Property; auto. apply Z'_Ord_Instantiate; auto.
      rewrite N'_Plus_Property,N'_Plus_Commutation,
      N'_Plus_Property; auto.
    + rewrite Z'_Plus_Instantiate; auto. apply R_N'_Property;
      try apply N'_Plus_in_N'; try apply N'_Plus_in_N'; auto.
      rewrite N'_Plus_Property,N'_Plus_Association,
      (N'_Plus_Commutation a),<-N'_Plus_Association; auto.
    + intros x0 [H18[]]. apply AxiomII in H18 as [H18[z[]]].
      apply AxiomII in H21 as [H21[j[k[H23[]]]]].
      rewrite H22,H23 in *. rewrite Z'_Plus_Instantiate in H20; auto.
      apply R_N'_Property in H20; try apply N'_Plus_in_N'; auto.
      apply R_N'_Property; auto.
      rewrite (N'_Plus_Commutation _ j),N'_Plus_Property; auto.
      rewrite (N'_Plus_Association n),(N'_Plus_Commutation k),
      <-(N'_Plus_Association n) in H20; auto. rewrite <-H14 in H20.
      rewrite N'_Plus_Association,(N'_Plus_Commutation j),
      <-(N'_Plus_Association m),(N'_Plus_Association _ a)
      in H20; try apply N'_Plus_in_N'; auto.
      apply N'_Plus_Cancellation in H20; try apply N'_Plus_in_N'; auto.
  - destruct H12 as [z[[H12[]]]]. apply Z'_Ord_Instantiate; auto.
    apply AxiomII in H12 as [H12[z0[]]].
    apply AxiomII in H16 as [H16[j[k[H18[]]]]].
    rewrite H17,H18 in *. rewrite Z'_Plus_Instantiate in H14; auto.
    apply R_N'_Property in H14; try apply N'_Plus_in_N'; auto.
    pose proof H; pose proof in_ω_0. eapply Fn_in_N' in H22; destruct H21; eauto.
    assert (k < j).
    { rewrite Z'0_Property in H13; auto.
      apply Z'_Ord_Instantiate in H13; auto.
      rewrite N'_Plus_Commutation,(N'_Plus_Commutation _ j),
      N'_Plus_Property,N'_Plus_Property in H13; auto. }
    rewrite (N'_Plus_Commutation m),(N'_Plus_Commutation n),
    N'_Plus_Association,N'_Plus_Association in H14; auto.
    assert ((m + q) ∈ N' /\ (n + p) ∈ N') as [].
    { split; apply N'_Plus_in_N'; auto. }
    apply (N'_Ord_Tri _ (n + p)) in H25 as [H25|[|]]; auto.
    + apply (N'_Plus_PrOrder _ _ k) in H25;
      try apply N'_Plus_in_N'; auto. rewrite <-H14,
      (N'_Plus_Commutation j),(N'_Plus_Commutation k) in H25;
      try apply N'_Plus_in_N'; auto.
      apply N'_Plus_PrOrder in H25; try apply N'_Plus_in_N'; auto.
      apply (N'_Ord_Trans k j k) in H25; auto.
      elim (N'_Ord_irReflex_weak k); auto.
    + rewrite (N'_Plus_Commutation j),(N'_Plus_Commutation k),
      H25 in H14; try apply N'_Plus_in_N'; auto. apply
      N'_Plus_Cancellation in H14; try apply N'_Plus_in_N'; auto.
      rewrite H14 in H24. elim (N'_Ord_irReflex k k); auto.
  Close Scope n'_scope.
Qed.

(* 验证 *Z中负元的性质:
       对任意*Z中的元u, 存在唯一的负元v使得 u+v=0.
       [注: 此性质是*N所不具备的, 同时也是利用等价类构造*Z的目的.] *)
Property Z'_Neg : ∀ u, u ∈ Z' -> (∃! v, v ∈ Z' /\ (u + v) = Z'0).
Proof.
  destruct NPAUF as [H _].
  intros. pose proof H0 as Ha.
  apply AxiomII in H0 as [H0[a[]]].
  apply AxiomII in H1 as [H1[x[y[H3[]]]]].
  rewrite H3 in *. clear dependent a.
  exists (\[[y,x]\]).
  assert (\[[y,x]\] ∈ Z').
  { apply Z'_Instantiate2; auto. }
  assert (u + \[[y,x]\] = Z'0).
  { rewrite H2,Z'_Plus_Instantiate; auto. rewrite Z'0_Property; auto.
    pose proof in_ω_0. eapply Fn_in_N' in H6; destruct H; eauto.
    apply R_N'_Property; try apply N'_Plus_in_N';
    try split; auto. rewrite N'_Plus_Property,N'_Plus_Property,
    N'_Plus_Commutation; try apply N'_Plus_in_N'; try split; auto. }
  repeat split; auto. intros v [].
  assert (\[[y,x]\] = (u + \[[y,x]\]) + v).
  { rewrite Z'_Plus_Association,(Z'_Plus_Commutation _ v),
    <-Z'_Plus_Association,H8,Z'_Plus_Commutation,Z'_Plus_Property;
    auto. apply Z'0_in_Z'; auto. }
  assert (v = (u + \[[y,x]\]) + v).
  { rewrite H6,Z'_Plus_Commutation,Z'_Plus_Property; auto.
    apply Z'0_in_Z'; auto. }
  rewrite H10,<-H9; auto.
Qed.

(* 负元的具体化:
      对任意*N中的元m n 和 *Z中的元u, 若[m,n] + u = 0, 则u = [n,m].  *)
Property Z'_Neg_Instantiate : ∀ m n u, m ∈ N' -> n ∈ N' -> u ∈ Z'
  -> \[[m,n]\] + u = Z'0 -> u = \[[n,m]\].
Proof.
  destruct NPAUF as [H _].
  intros. apply AxiomII in H2 as [H2[x[]]].
  apply AxiomII in H4 as [H4[a[b[H6[]]]]]. rewrite H5,H6 in *.
  rewrite Z'_Plus_Instantiate,Z'0_Property in H3; auto.
  pose proof in_ω_0. pose proof H.
  eapply Fn_in_N' in H9; destruct H10; eauto.
  apply R_N'_Property in H3; try apply N'_Plus_in_N'; auto.
  rewrite N'_Plus_Property,N'_Plus_Property in H3;
  try apply N'_Plus_in_N'; auto. apply R_N'_Property; auto.
  rewrite N'_Plus_Commutation,(N'_Plus_Commutation b); auto.
Qed.

Property Z'_Mult_Property1 : ∀ u, u ∈ Z' -> u · Z'0 = Z'0.
Proof.
  intros. apply AxiomII in H as [H[x[]]].
  apply AxiomII in H0 as [H0[x0[y0[H2[]]]]].
  rewrite H2 in *. clear dependent x.
  pose proof in_ω_0. pose proof H as Ha. apply Fn_in_N' in H2.
  rewrite H1,Z'0_Property,Z'_Mult_Instantiate; auto.
  apply R_N'_Property; try apply N'_Plus_in_N';
  try apply N'_Mult_in_N'; auto.
Qed.

(* 验证 *Z中的关于单位元的性质: u * Z'1 = u *)
Property Z'_Mult_Property2 : ∀ u, u ∈ Z' -> u · Z'1 = u.
Proof.
  intros. apply AxiomII in H as [H[x[]]].
  apply AxiomII in H0 as [H0[x0[y0[H2[]]]]].
  rewrite H2 in *. clear dependent x. destruct MKT135.
  pose proof in_ω_1. pose proof H as Ha.
  destruct Ha as [Ha Hb]. clear Hb.
  apply Fn_in_N' in H2. apply Fn_in_N' in H6.
  rewrite H1,Z'1_Property,Z'_Mult_Instantiate; auto.
  apply R_N'_Property; try apply N'_Plus_in_N';
  try apply N'_Mult_in_N'; auto.
  rewrite N'_Mult_Property1,N'_Mult_Property1,N'_Mult_Property2,
  N'_Mult_Property2,N'_Plus_Property,(N'_Plus_Commutation (F 0)),
  N'_Plus_Property,N'_Plus_Commutation; auto.
Qed.

(* 无零因子 *)
Property Z'_Mult_Property3 : ∀ u v, u ∈ Z' -> v ∈ Z' -> u · v = Z'0
  -> u = Z'0 \/ v = Z'0.
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _].
  intros. apply AxiomII in H0 as [H0[x[]]].
  apply AxiomII in H3 as [H3[m[n[H5[]]]]].
  apply AxiomII in H1 as [H1[y[]]].
  apply AxiomII in H8 as [H8[p[q[H10[]]]]].
  rewrite H4,H9,H5,H10 in *.
  rewrite Z'_Mult_Instantiate in H2; auto.
  rewrite Z'0_Property in *; auto.
  pose proof in_ω_0. pose proof H.
  eapply Fn_in_N' in H13; destruct H14; eauto.
  apply R_N'_Property in H2; try apply N'_Plus_in_N';
  try apply N'_Mult_in_N'; auto.
  rewrite N'_Plus_Property,N'_Plus_Property in H2;
  try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
  assert (∀ a b c d, a ∈ N' -> b ∈ N' -> c ∈ N'
    -> d ∈ N' -> (a · c) + (b · d)
    = (a · d) + (b · c) -> ~ (a < b /\ c < d)).
  { intros. intro. destruct H21.
    apply N'_Plus_PrOrder_Corollary in H21 as [i[[H21[]]]]; auto.
    apply N'_Plus_PrOrder_Corollary in H22 as [j[[H22[]]]]; auto.
    rewrite <-H24,<-H27 in H20.
    rewrite N'_Mult_Distribution,
    N'_Mult_Distribution,N'_Plus_Association in H20;
    try apply N'_Mult_in_N'; try apply N'_Plus_in_N'; auto.
    apply N'_Plus_Cancellation in H20; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; try apply N'_Plus_in_N'; auto.
    rewrite (N'_Mult_Commutation _ c),
    (N'_Mult_Commutation _ j),
    N'_Mult_Distribution,N'_Mult_Distribution,
    (N'_Plus_Commutation (a · j)) in H20;
    try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
    apply N'_Plus_Cancellation in H20; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; auto.
    rewrite (N'_Mult_Commutation a j) in H20; auto.
    assert (j · a = (j · a) + (F 0)).
    { rewrite N'_Plus_Property; try apply N'_Mult_in_N'; auto. }
    assert ((j · a) + (j · i) = (j · a) + (F 0)). { rewrite <-H29; auto. }
    apply N'_Plus_Cancellation in H30;
    try apply N'_Mult_in_N'; auto.
    apply N'_Mult_Property3 in H30; auto. destruct H30;
    [rewrite <-H30 in H26; elim (N'_Ord_irReflex_weak j)|
     rewrite <-H30 in H23; elim (N'_Ord_irReflex_weak i)];
    destruct H; auto. }
  assert (m ∈ N' /\ n ∈ N') as []; auto.
  apply (N'_Ord_Tri m n) in H17; auto; clear H18.
  assert (p ∈ N' /\ q ∈ N') as []; auto.
  apply (N'_Ord_Tri p q) in H18; auto; clear H19.
  destruct H17 as [H17|[|]].
  - destruct H18 as [H18|[|]].
    + elim (H16 m n p q); auto.
    + elim (H16 m n q p); auto.
    + right. apply R_N'_Property; auto.
      rewrite N'_Plus_Property,N'_Plus_Property; auto.
  - destruct H18 as [H18|[|]].
    + elim (H16 n m p q); auto. rewrite N'_Plus_Commutation,
      (N'_Plus_Commutation (n · q));
      try apply N'_Mult_in_N'; auto.
    + elim (H16 n m q p); auto. rewrite N'_Plus_Commutation,
      (N'_Plus_Commutation (n · p));
      try apply N'_Mult_in_N'; auto.
    + right. apply R_N'_Property; auto.
      rewrite N'_Plus_Property,N'_Plus_Property; auto.
  - left. apply R_N'_Property; auto.
    rewrite N'_Plus_Property,N'_Plus_Property; auto.
  Close Scope n'_scope.
Qed.

(* 验证 *Z中的乘法满足交换律. *)
Property Z'_Mult_Commutation : ∀ u v, u ∈ Z' -> v ∈ Z' -> u · v = v · u.
Proof.
  intros. apply AxiomII in H as [H[x[]]]. apply AxiomII in H1
  as [H1[x0[y0[H3[]]]]]. apply AxiomII in H0 as [H0[y[]]].
  apply AxiomII in H6 as [H6[x1[y1[H8[]]]]]. rewrite H3,H8 in *.
  rewrite H2,H7. rewrite Z'_Mult_Instantiate,Z'_Mult_Instantiate; auto.
  rewrite (N'_Mult_Commutation x0 x1),
  (N'_Mult_Commutation y0 y1),(N'_Mult_Commutation x0 y1),
  (N'_Mult_Commutation y0 x1),(N'_Plus_Commutation
  (y1 · x0)%n'); try apply N'_Mult_in_N'; auto.
Qed.

(* 验证 *Z中的乘法满足结合律 *)
Property Z'_Mult_Association : ∀ u v w, u ∈ Z' -> v ∈ Z' -> w ∈ Z'
  -> (u · v) · w = u · (v · w).
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _].
  intros. apply AxiomII in H0 as [H0[a[]]].
  apply AxiomII in H3 as [H3[x0[y0[H5[]]]]].
  apply AxiomII in H1 as [H1[b[]]].
  apply AxiomII in H8 as [H8[x1[y1[H10[]]]]].
  apply AxiomII in H2 as [H2[c[]]].
  apply AxiomII in H13 as [H13[x2[y2[H15[]]]]].
  rewrite H4,H9,H14 in *. rewrite H5,H10,H15,Z'_Mult_Instantiate,
  Z'_Mult_Instantiate,Z'_Mult_Instantiate,Z'_Mult_Instantiate;
  try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
  assert (((((x0 · x1) + (y0 · y1)) · x2) + (((x0 · y1) + (y0 · x1)) · y2))
    = ((x0 · ((x1 · x2) + (y1 · y2))) + (y0 · ((x1 · y2) + (y1 · x2))))).
  { rewrite (N'_Mult_Commutation _ x2),
    (N'_Mult_Commutation _ y2),
    (N'_Plus_Commutation (x1 · y2)),N'_Mult_Distribution,
    N'_Mult_Distribution,N'_Mult_Distribution,N'_Mult_Distribution,
    (N'_Mult_Commutation x2),(N'_Mult_Commutation x2),
    (N'_Mult_Commutation y2),(N'_Mult_Commutation y2),
    N'_Plus_Association,
    <-(N'_Plus_Association ((y0 · y1) · x2)),
    (N'_Plus_Commutation ((y0 · y1) · x2)),
    (N'_Plus_Association ((x0 · y1) · y2)),
    <-(N'_Plus_Association ((x0 · x1) · x2)),
    (N'_Mult_Association x0),(N'_Mult_Association x0),
    (N'_Mult_Association y0),(N'_Mult_Association y0);
    try apply N'_Plus_in_N'; try apply N'_Mult_in_N';
    try apply N'_Mult_in_N'; auto. }
  assert (((((x0 · x1) + (y0 · y1)) · y2) + (((x0 · y1) + (y0 · x1)) · x2))
    = ((x0 · ((x1 · y2) + (y1 · x2))) + (y0 · ((x1 · x2) + (y1 · y2))))).
  { rewrite (N'_Mult_Commutation _ y2),
    (N'_Mult_Commutation _ x2),
    (N'_Plus_Commutation (x1 · x2)),N'_Mult_Distribution,
    N'_Mult_Distribution,N'_Mult_Distribution,N'_Mult_Distribution,
    (N'_Mult_Commutation y2),(N'_Mult_Commutation y2),
    (N'_Mult_Commutation x2),(N'_Mult_Commutation x2),
    N'_Plus_Association,
    <-(N'_Plus_Association ((y0 · y1) · y2)),
    (N'_Plus_Commutation ((y0 · y1) · y2)),
    (N'_Plus_Association ((x0 · y1) · x2)),
    <-(N'_Plus_Association ((x0 · x1) · y2)),
    (N'_Mult_Association x0),(N'_Mult_Association x0),
    (N'_Mult_Association y0),(N'_Mult_Association y0);
    try apply N'_Plus_in_N'; try apply N'_Mult_in_N';
    try apply N'_Mult_in_N'; auto. }
  rewrite H18,H19; auto.
  Close Scope n'_scope.
Qed.

(* 验证 *Z中的乘法满足分配律. *)
Property Z'_Mult_Distribution : ∀ u v w, u ∈ Z' -> v ∈ Z' -> w ∈ Z'
  -> u · (v + w) = (u · v) + (u · w).
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _].
  intros. apply AxiomII in H0 as [H0[a[]]].
  apply AxiomII in H3 as [H3[x0[y0[H5[]]]]].
  apply AxiomII in H1 as [H1[b[]]].
  apply AxiomII in H8 as [H8[x1[y1[H10[]]]]].
  apply AxiomII in H2 as [H2[c[]]].
  apply AxiomII in H13 as [H13[x2[y2[H15[]]]]].
  rewrite H4,H9,H14 in *.
  rewrite H5,H10,H15,Z'_Plus_Instantiate,Z'_Mult_Instantiate,
  Z'_Mult_Instantiate,Z'_Mult_Instantiate,Z'_Plus_Instantiate;
  try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
  rewrite N'_Mult_Distribution,N'_Mult_Distribution,
  N'_Mult_Distribution,N'_Mult_Distribution,
  (N'_Plus_Association (x0 · x1)),
  <-(N'_Plus_Association (x0 · x2)),
  (N'_Plus_Commutation(x0 · x2)),
  (N'_Plus_Association (y0 · y1)),
  <-(N'_Plus_Association (x0 · x1)),
  (N'_Plus_Association (x0 · y1)),
  <-(N'_Plus_Association (x0 · y2)),
  (N'_Plus_Commutation (x0 · y2)),
  (N'_Plus_Association (y0 · x1)),
  <-(N'_Plus_Association (x0 · y1));
  try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
  Close Scope n'_scope.
Qed.

(* 验证: 乘法消去律 *)
Property Z'_Mult_Cancellation : ∀ m n k, m ∈ Z' -> n ∈ Z' -> k ∈ Z'
  -> m <> Z'0 -> m · n = m · k -> n = k.
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _].
  intros. apply AxiomII in H0 as [H0[a[]]].
  apply AxiomII in H5 as [H5[x0[y0[H7[]]]]].
  apply AxiomII in H1 as [H1[b[]]].
  apply AxiomII in H10 as [H10[x1[y1[H12[]]]]].
  apply AxiomII in H2 as [H2[c[]]].
  apply AxiomII in H15 as [H15[x2[y2[H17[]]]]].
  rewrite H6,H7,H11,H12,H16,H17 in *.
  rewrite Z'_Mult_Instantiate,Z'_Mult_Instantiate in H4; auto.
  apply R_N'_Property in H4; try apply N'_Plus_in_N';
  try apply N'_Mult_in_N'; auto. apply R_N'_Property; auto.
  rewrite N'_Plus_Association,N'_Plus_Association,
  <-(N'_Plus_Association (y0 · y1)),
  <-(N'_Plus_Association (y0 · x1)),
  (N'_Plus_Commutation (y0 · y1)),
  (N'_Plus_Commutation (y0 · x1)),
  N'_Plus_Association,N'_Plus_Association,
  <-(N'_Plus_Association (x0 · x1)),
  <-(N'_Plus_Association (x0 · y1)),
  <-N'_Mult_Distribution,<-N'_Mult_Distribution,
  <-N'_Mult_Distribution,<-N'_Mult_Distribution in H4;
  try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
  assert (∀ A B, A ∈ N' -> B ∈ N' -> (x0 · A) + (y0 · B)
    = (x0 · B) + (y0 · A) -> ~ A < B).
  { intros. intro.
    apply N'_Plus_PrOrder_Corollary in H23 as [C[[H24[]]]]; auto.
    rewrite <-H25 in H22.
    rewrite N'_Mult_Distribution,N'_Mult_Distribution,
    N'_Plus_Association in H22; try apply N'_Mult_in_N'; auto.
    apply N'_Plus_Cancellation in H22;
    try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
    rewrite (N'_Plus_Commutation (x0 · C)) in H22;
    try apply N'_Mult_in_N'; auto. apply N'_Plus_Cancellation
    in H22; try apply N'_Mult_in_N'; auto.
    rewrite N'_Mult_Commutation,(N'_Mult_Commutation x0)
    in H22; auto. pose proof in_ω_0; pose proof H.
    eapply Fn_in_N' in H27; destruct H28; eauto.
    apply N'_Mult_Cancellation in H22; auto. elim H3.
    rewrite Z'0_Property; auto. apply R_N'_Property; auto.
    rewrite N'_Plus_Property,N'_Plus_Property; auto. intro.
    rewrite <-H30 in H23. elim (N'_Ord_irReflex_weak C);
    destruct H; auto. }
  assert ((x1 + y2) ∈ N' /\ (y1 + x2) ∈ N') as [].
  { split; apply N'_Plus_in_N'; auto. }
  apply (N'_Ord_Tri _ (y1 + x2)) in H21; auto.
  destruct H21 as [H21|[]];
  [elim (H20 (x1 + y2) (y1 + x2))|
   elim (H20 (y1 + x2) (x1 + y2))|];
  try apply N'_Plus_in_N'; auto.
  Close Scope n'_scope.
Qed.

(* *Z上定义的 Z'_Ord关系 满足乘法保序 (需注意和 消去律 的区别).  *)
Property Z'_Mult_PrOrder : ∀ u v w, u ∈ Z' -> v ∈ Z' -> w ∈ Z' -> Z'0 < w
  -> u < v <-> (w · u) < (w · v).
Proof.
  Open Scope n'_scope.
  destruct NPAUF as [H _].
  intros. apply AxiomII in H0 as [H0[x[]]].
  apply AxiomII in H4 as [H4[m[n[H6[]]]]].
  apply AxiomII in H1 as [H1[y[]]].
  apply AxiomII in H9 as [H9[p[q[H11[]]]]].
  apply AxiomII in H2 as [H2[z[]]].
  apply AxiomII in H14 as [H14[j[k[H16[]]]]].
  rewrite H5,H10,H15,H6,H11,H16 in *.
  rewrite Z'0_Property in H3; auto.
  pose proof in_ω_0; pose proof H.
  eapply Fn_in_N' in H19; destruct H20; eauto; clear H20 H21.
  apply Z'_Ord_Instantiate in H3; auto.
  rewrite (N'_Plus_Commutation _ k),(N'_Plus_Commutation _ j),
  N'_Plus_Property,N'_Plus_Property in H3; auto.
  apply N'_Plus_PrOrder_Corollary in H3 as [e[[H3[]]]]; auto.
  rewrite <-H21. split; intros.
  - apply Z'_Ord_Instantiate in H23; auto.
    rewrite Z'_Mult_Instantiate,Z'_Mult_Instantiate;
    try apply N'_Plus_in_N'; auto.
    apply Z'_Ord_Instantiate; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; try apply N'_Plus_in_N'; auto.
    rewrite (N'_Mult_Commutation _ m),
    (N'_Mult_Commutation _ q),
    (N'_Mult_Commutation (k + e) n),
    (N'_Mult_Commutation (k + e) p),
    N'_Mult_Distribution,N'_Mult_Distribution,
    N'_Mult_Distribution,N'_Mult_Distribution,
    (N'_Plus_Commutation _ (k · n)),
    (N'_Plus_Association (k · n)),
    (N'_Plus_Association _ (k · m)),
    (N'_Plus_Association (n · k)),
    (N'_Mult_Commutation k n); try apply N'_Plus_in_N';
    try apply N'_Plus_in_N'; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; auto.
    apply N'_Plus_PrOrder; try apply N'_Plus_in_N'; try apply
    N'_Plus_in_N'; try apply N'_Plus_in_N'; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; auto.
    rewrite <-(N'_Plus_Association (n · e)),
    (N'_Plus_Commutation (n · e)),
    (N'_Plus_Association (m · k)),
    (N'_Plus_Association (k · m)),
    (N'_Mult_Commutation m k); try apply N'_Plus_in_N';
    try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
    apply N'_Plus_PrOrder; try apply N'_Plus_in_N';
    try apply N'_Plus_in_N'; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; auto.
    rewrite N'_Plus_Association,N'_Plus_Association,
    (N'_Plus_Commutation (q · e)),
    (N'_Plus_Commutation (p · e)),
    <-(N'_Plus_Association (q · k)),
    <-(N'_Plus_Association (p · k)),
    <-(N'_Plus_Association (m · e)),
    <-(N'_Plus_Association (n · e)),
    (N'_Plus_Commutation (m · e)),
    (N'_Plus_Commutation (n · e)),
    (N'_Plus_Association _ (m · e) _),
    (N'_Plus_Association _ (n · e) _),
    (N'_Plus_Commutation (q · k)),
    (N'_Mult_Commutation k p),(N'_Mult_Commutation q k);
    try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
    apply N'_Plus_PrOrder; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; auto.
    rewrite (N'_Mult_Commutation m),(N'_Mult_Commutation q),
    (N'_Mult_Commutation n),(N'_Mult_Commutation p),
    <-N'_Mult_Distribution,<-N'_Mult_Distribution; auto.
    apply N'_Mult_PrOrder; try apply N'_Plus_in_N'; auto. intro.
    rewrite <-H24 in H20. elim (N'_Ord_irReflex e e); auto.
  - apply Z'_Ord_Instantiate; auto.
    rewrite Z'_Mult_Instantiate,Z'_Mult_Instantiate in H23;
    try apply N'_Plus_in_N'; auto. apply Z'_Ord_Instantiate in H23;
    try apply N'_Plus_in_N'; try apply N'_Mult_in_N';
    try apply N'_Plus_in_N'; auto.
    rewrite (N'_Mult_Commutation _ m),
    (N'_Mult_Commutation _ q),
    (N'_Mult_Commutation (k + e) n),
    (N'_Mult_Commutation (k + e) p),
    N'_Mult_Distribution,N'_Mult_Distribution,
    N'_Mult_Distribution,N'_Mult_Distribution,
    (N'_Plus_Commutation _ (k · n)),
    (N'_Plus_Association (k · n)),
    (N'_Plus_Association _ (k · m)),
    (N'_Plus_Association (n · k)),
    (N'_Mult_Commutation k n) in H23; try apply N'_Plus_in_N';
    try apply N'_Plus_in_N'; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; auto.
    apply N'_Plus_PrOrder in H23; try apply N'_Plus_in_N';
    try apply N'_Plus_in_N'; try apply N'_Plus_in_N';
    try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
    rewrite <-(N'_Plus_Association (n · e)),
    (N'_Plus_Commutation (n · e)),
    (N'_Plus_Association (m · k)),
    (N'_Plus_Association (k · m)),
    (N'_Mult_Commutation m k) in H23; try apply N'_Plus_in_N';
    try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
    apply N'_Plus_PrOrder in H23; try apply N'_Plus_in_N';
    try apply N'_Plus_in_N'; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; auto. rewrite N'_Plus_Association,
    N'_Plus_Association,(N'_Plus_Commutation (q · e)),
    (N'_Plus_Commutation (p · e)),
    <-(N'_Plus_Association (q · k)),
    <-(N'_Plus_Association (p · k)),
    <-(N'_Plus_Association (m · e)),
    <-(N'_Plus_Association (n · e)),
    (N'_Plus_Commutation (m · e)),
    (N'_Plus_Commutation (n · e)),
    (N'_Plus_Association _ (m · e) _),
    (N'_Plus_Association _ (n · e) _),
    (N'_Plus_Commutation (q · k)),
    (N'_Mult_Commutation k p),(N'_Mult_Commutation q k)
    in H23; try apply N'_Plus_in_N'; try apply N'_Mult_in_N'; auto.
    apply N'_Plus_PrOrder in H23; try apply N'_Plus_in_N';
    try apply N'_Mult_in_N'; auto. rewrite
    (N'_Mult_Commutation m),(N'_Mult_Commutation q),
    (N'_Mult_Commutation n),(N'_Mult_Commutation p),
    <-N'_Mult_Distribution,<-N'_Mult_Distribution in H23; auto.
    apply N'_Mult_PrOrder in H23; try apply N'_Plus_in_N'; auto.
    intro. rewrite <-H25 in H20.
    elim (N'_Ord_irReflex e e); auto.
  Close Scope n'_scope.
Qed.

(* 关于*Z的一些其他性质 *)
Property Z'_otherPropertys1 : ∀ a b, a ∈ (Z' ~ [Z'0]) -> b ∈ (Z' ~ [Z'0])
  -> (a · b) ∈ (Z' ~ [Z'0]).
Proof.
  intros. apply MKT4'. apply MKT4' in H as [].
  apply MKT4' in H0 as []. split. apply Z'_Mult_in_Z'; auto.
  apply AxiomII; split. apply (Z'_Mult_in_Z' a b) in H; eauto.
  pose proof Z'0_in_Z'. intro. apply MKT41 in H4; eauto.
  apply Z'_Mult_Property3 in H4; auto. apply AxiomII in H1 as [].
  apply AxiomII in H2 as []. destruct H4; [elim H5|elim H6]; apply MKT41; eauto.
Qed.

Global Hint Resolve Z'_otherPropertys1 : Z'.

Property Z'_otherPropertys2 : ∀ a b, a ∈ Z' -> b ∈ Z' -> Z'0 < a
  -> Z'0 < b -> Z'0 < (a · b).
Proof.
  intros. replace Z'0 with (a · Z'0).
  apply Z'_Mult_PrOrder; auto with Z'.
  rewrite Z'_Mult_Property1; auto.
Qed.

Global Hint Resolve Z'_otherPropertys2 : Z'.

Property Z'_otherPropertys3 : ∀ a, a ∈ (Z' ~ [Z'0]) -> Z'0 < (a · a).
Proof.
  intros. assert (a ∈ Z' /\ a <> Z'0) as [].
  { apply MKT4' in H as []. apply AxiomII in H0 as [].
    split; auto. intro. elim H1. pose proof Z'0_in_Z'. apply MKT41; eauto. }
  assert ((F 0) ∈ N'). { apply Fn_in_N'; try apply in_ω_0. }
  assert (Z'0 ∈ Z' /\ a ∈ Z') as []. { split; auto with Z'. }
  apply (Z'_Ord_Tri _ a) in H3 as [H3|[|]]; auto.
  - replace Z'0 with (a · Z'0).
    apply Z'_Mult_PrOrder; auto with Z'.
    rewrite Z'_Mult_Property1; auto.
  - pose proof Z'0_in_Z'.
    apply Z'_Plus_PrOrder_Corollary in H3 as [a0[[H3[]]_]]; auto.
    assert (a · (a + a0) = a · Z'0). { rewrite H7; auto. }
    rewrite Z'_Mult_Distribution,Z'_Mult_Property1,
    Z'_Plus_Commutation,(Z'_Mult_Commutation a a0) in H8; auto with Z'.
    assert (a0 · (a + a0) = a0 · Z'0). { rewrite H7; auto. }
    rewrite Z'_Mult_Distribution,Z'_Mult_Property1 in H9; auto.
    assert ((a0 · a) ∈ Z'); auto with Z'.
    apply Z'_Neg in H10 as [x[_]]; auto.
    assert (x = a · a /\ x = a0 · a0) as [].
    { split; apply H10; split; auto with Z'. }
    rewrite <-H11,H12. apply Z'_otherPropertys2; auto.
  - elim H1; auto.
Qed.

Global Hint Resolve Z'_otherPropertys3 : Z'.

(* *Z中 异号元素相乘小于零 *)
Property Z'_otherPropertys4 : ∀ a b, a ∈ Z' -> b ∈ Z' -> Z'0 < a
  -> b < Z'0 -> (a · b) < Z'0.
Proof.
  intros. pose proof H2. apply Z'_Plus_PrOrder_Corollary in H3
  as [b0[[H3[]]]]; auto with Z'.
  assert (a · (b + b0) = a · Z'0). { rewrite H5; auto. }
  rewrite Z'_Mult_Property1,Z'_Mult_Distribution in H7; auto.
  assert (Z'0 < (a · b0)); auto with Z'.
  assert ((a · b) ∈ Z' /\ Z'0 ∈ Z') as []. { split; auto with Z'. }
  apply (Z'_Ord_Tri _ Z'0) in H9 as [H9|[]]; auto.
  - apply (Z'_Plus_PrOrder _ _ (a · b)) in H8; auto with Z'.
    rewrite Z'_Plus_Property in H8; auto with Z'. rewrite H7 in H8; auto.
  - rewrite H9,Z'_Plus_Commutation,Z'_Plus_Property in H7; auto with Z'.
    rewrite H7 in H8. elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
Qed.

Global Hint Resolve Z'_otherPropertys4 : Z'.

(* *Z中 两个元素相乘大于零 则 两个元素同号 *)
Property Z'_otherPropertys5 : ∀ a b, a ∈ Z' -> b ∈ Z' -> Z'0 < (a · b)
  -> (Z'0 < a /\ Z'0 < b) \/ (a < Z'0 /\ b < Z'0).
Proof.
  destruct NPAUF as [H _]. intros.
  assert (Z'0 ∈ Z' /\ a ∈ Z') as []. { split; auto with Z'. }
  apply (Z'_Ord_Tri _ a) in H3; auto; clear H4.
  assert (Z'0 ∈ Z' /\ b ∈ Z') as [].
  { split; auto with Z'. }
  apply (Z'_Ord_Tri _ b) in H4; auto; clear H5.
  destruct H3 as [H3|[]].
  - destruct H4 as [H4|[]]; auto.
    + apply (Z'_otherPropertys4 a b) in H3; auto.
      apply (Z'_Ord_Trans _ _ Z'0) in H2; auto with Z'.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
    + rewrite <-H4,Z'_Mult_Property1 in H2; auto.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
  - destruct H4 as [H4|[]]; auto.
    + apply (Z'_otherPropertys4 b a) in H3; auto.
      rewrite Z'_Mult_Commutation in H2; auto.
      apply (Z'_Ord_Trans _ _ Z'0) in H2; auto with Z'.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
    + rewrite <-H4,Z'_Mult_Property1 in H2; auto.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
  - rewrite <-H3,Z'_Mult_Commutation,Z'_Mult_Property1 in H2;
    auto with Z'.
    elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
Qed.

Global Hint Resolve Z'_otherPropertys5 : Z'.

(* *Z中 两个元素相乘小于零 则 两个元素异号 *)
Property Z'_otherPropertys6 : ∀ a b, a ∈ Z' -> b ∈ Z' -> (a · b) < Z'0
  -> (Z'0 < a /\ b < Z'0) \/ (a < Z'0 /\ Z'0 < b).
Proof.
  destruct NPAUF as [H _]. intros.
  assert (Z'0 ∈ Z' /\ a ∈ Z') as []. { split; auto with Z'. }
  apply (Z'_Ord_Tri _ a)  in H3; auto; clear H4.
  assert (Z'0 ∈ Z' /\ b ∈ Z') as []. { split; auto with Z'. }
  apply (Z'_Ord_Tri _ b)  in H4; auto; clear H5.
  destruct H3 as [H3|[]].
  - destruct H4 as [H4|[]]; auto.
    + apply (Z'_otherPropertys2 a b) in H3; auto.
      apply (Z'_Ord_Trans _ _ Z'0) in H3; auto with Z'.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
    + rewrite <-H4,Z'_Mult_Property1 in H2; auto.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
  - destruct H4 as [H4|[]]; auto.
    + apply Z'_Plus_PrOrder_Corollary in H3 as [a0[[H3[]]]];
      apply Z'_Plus_PrOrder_Corollary in H4 as [b0[[H4[]]]];
      auto with Z'. clear H7 H10.
      assert (a · b = a0 · b0).
      { assert (a · (b + b0) = b0 · (a + a0)).
        { rewrite H9,H6,Z'_Mult_Property1,Z'_Mult_Property1; auto. }
        rewrite Z'_Mult_Distribution,Z'_Mult_Distribution,
        Z'_Plus_Commutation,Z'_Mult_Commutation,
        (Z'_Mult_Commutation b0 a0) in H7; auto with Z'.
        apply Z'_Plus_Cancellation in H7; auto with Z'. }
      pose proof H3. apply (Z'_otherPropertys2 a0 b0) in H3; auto.
      rewrite H7 in H2. apply (Z'_Ord_Trans _ _ Z'0) in H3; auto with Z'.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
    + rewrite <-H4,Z'_Mult_Property1 in H2; auto.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
  - rewrite <-H3,Z'_Mult_Commutation,Z'_Mult_Property1 in H2;
    auto with Z'.
    elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
Qed.

Global Hint Resolve Z'_otherPropertys6 : Z'.

(* *Z中 大于零的元素一定大于等于一 *)
Property Z'_otherPropertys7 : ∀ a, a ∈ Z' -> Z'0 < a -> Z'1 < a \/ Z'1 = a.
Proof.
  destruct NPAUF as [H _].
  intros. pose proof H0. apply (Z'_Ord_Tri Z'1)
  in H2 as [|[|]]; auto with Z'. inZ' H0 m n.
  rewrite Z'0_Property,H4 in H1; auto.
  rewrite Z'1_Property,H4 in H2; auto.
  pose proof H. destruct H5 as [_[H5 _]].
  apply Z'_Ord_Instantiate in H1,H2; try apply Fn_in_N'; auto;
  [ |apply in_ω_1]. rewrite N'_Plus_Commutation,
  N'_Plus_Property,N'_Plus_Commutation,N'_Plus_Property
  in H1; try apply Fn_in_N'; auto.
  rewrite N'_Plus_Property in H2; auto.
  apply N'_Plus_PrOrder_Corollary in H1 as [x[[H1[]]_]]; auto.
  rewrite <-H7 in H2. apply N'_Plus_PrOrder in H2;
  try apply Fn_in_N',in_ω_1; auto. clear H7.
  pose proof in_ω_0; pose proof in_ω_1.
  apply (F_Const_Fa F0 ω) in H7,H8; auto.
  apply AxiomII in H1 as [H1[f[H9[H10[]]]]].
  rewrite <-H7,H12 in H6. rewrite <-H8,H12 in H2.
  assert (Ensemble 0 /\ Ensemble 1) as [].
  { pose proof in_ω_0. pose proof in_ω_1. eauto. }
  assert (ω <> Φ) as HH.
  { intro. pose proof in_ω_0. rewrite H15 in H16. elim (@ MKT16 0); auto. }
  apply (Const_is_Function ω) in H13 as [H13[]], H14 as [H14[]]; auto.
  assert (ran(Const 0) ⊂ ω /\ ran(Const 1) ⊂ ω) as [].
  { rewrite H16,H18. split; unfold Included; intros;
    apply MKT41 in H19; try rewrite H19; auto. apply in_ω_1. }
  apply N'_Ord_Instantiate in H2,H6; auto.
  assert (\{ λ w, f[w] ∈ (Const 1)[w] \}
    ∩ \{ λ w, (Const 0)[w] ∈ f[w] \} = Φ).
  { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
    apply MKT4' in H21 as []. apply AxiomII in H21 as [];
    apply AxiomII in H22 as [].
    assert (z ∈ ω).
    { apply NNPP; intro. rewrite <-H15 in H25. apply MKT69a in H25.
      rewrite H25 in H24. elim MKT39. eauto. }
    assert ((Const 1)[z] = 1).
    { pose proof in_ω_1. rewrite <-H17 in H25.
      apply Property_Value,Property_ran in H25; auto.
      rewrite H18 in H25. apply MKT41 in H25; eauto. }
    assert ((Const 0)[z] = 0).
    { pose proof in_ω_0. rewrite <-H15 in H25.
      apply Property_Value,Property_ran in H25; auto.
      rewrite H16 in H25. apply MKT41 in H25; eauto. }
    rewrite H26 in H23. rewrite H27 in H24.
    apply MKT41 in H23; eauto. rewrite H23 in H24.
    elim (@ MKT16 0); auto. }
  apply AxiomII in H5 as [H5[[H22[H23[H24[]]]]]].
  elim H23. rewrite <-H21. apply H25; auto.
Qed.

Global Hint Resolve Z'_otherPropertys7 : Z'.



(* 定义一个新的类: 该类的形象为:

     { [F0,F0]  [F1,F0]  [F2,F0]  ...  [Fn,F0]  ...  [t1,F0]  [t2,F0]  ... }

     [注: '[Fn,F0]'表示以序偶[Fn,F0]为代表的等价类, Fn为主超滤.  ]
   此类实际为*N在*Z中的嵌入                                  *)
Definition Z'_N' := \{ λ u, ∃ m, m ∈ N' /\ u = \[[m,(F 0)]\] \}.

(* *Z_*N 是一个集 *)
Property Z'_N'_is_Set : Ensemble Z'_N'.
Proof.
  apply (MKT33 Z'). apply Z'_is_Set; auto.
  unfold Included; intros. apply AxiomII in H as [H[x[]]].
  apply AxiomII; split; auto. exists [x,(F 0)]. split; auto.
  apply AxiomII'. pose proof in_ω_0. apply Fn_in_N' in H2.
  repeat split; auto. apply MKT49a; eauto.
Qed.

(* *Z_*N是*Z的真子集  *)
Property Z'_N'_propersubset_Z' : Z'_N' ⊂ Z' /\ Z'_N' <> Z'.
Proof.
  destruct NPAUF as [H _]. split.
  - unfold Included; intros. apply AxiomII in H0 as [H0[x[]]].
    apply AxiomII; split; auto. exists ([x, F 0]). split; auto.
    apply AxiomII'. pose proof in_ω_0. eapply Fn_in_N' in H3;
    destruct H; eauto. split; auto. apply MKT49a; eauto.
  - intro. assert ((F 0) ∈ N' /\ (F 1) ∈ N') as [].
    { pose proof in_ω_0; pose proof in_ω_1.
      apply Fn_in_N' in H1; apply Fn_in_N' in H2; auto. }
    assert (\[[(F 0),(F 1)]\] ∈ Z').
    { apply AxiomII; split. apply (MKT33 N'×N').
      apply MKT74; apply N'_is_Set; destruct H; auto.
      unfold Included; intros. apply AxiomII in H3; tauto.
      exists ([(F 0),(F 1)]). split; auto.
      apply AxiomII'; split; auto. apply MKT49a; eauto. }
    rewrite <-H0 in H3. apply AxiomII in H3 as [H3[m[]]].
    apply R_N'_Property in H5; auto. pose proof N'_Ord_Tri.
    assert (Ensemble 0 /\ Ensemble 1) as [].
    { pose proof in_ω_0; pose proof in_ω_1; eauto. }
    assert (ω <> 0) as HH.
    { intro. pose proof in_ω_0. rewrite H9 in H10. elim (@ MKT16 0); auto. }
    apply (Const_is_Function ω) in H7 as [H7[]];
    apply (Const_is_Function ω) in H8 as [H8[]]; auto.
    assert (ran(Const 0) ⊂ ω /\ ran(Const 1) ⊂ ω) as [].
    { rewrite H10,H12. pose proof in_ω_0; pose proof in_ω_1.
      split; unfold Included; intros; apply MKT41 in H15; eauto;
      rewrite H15; auto. }
    assert ((F 0) ∈ N' /\ m ∈ N') as []; auto.
    apply (H6 _ m) in H15 as [H15|[|]]; auto; clear H16.
    + apply (N'_Plus_PrOrder _ _ (F 0)) in H15; auto.
      rewrite H5 in H15. rewrite N'_Plus_Commutation,
      (N'_Plus_Commutation _ m) in H15; auto.
      apply N'_Plus_PrOrder in H15; auto.
      assert ((Const 0)〈F0〉 = F 0 /\ (Const 1)〈F0〉 = F 1)%n' as [].
      { split; apply F_Const_Fa; destruct H as [_[]];
        try apply in_ω_0; try apply in_ω_1; auto. }
      rewrite <-H16,<-H17 in H15.
      apply N'_Ord_Instantiate in H15; auto.
      assert (\{ λ w, (Const 1)[w] ∈ (Const 0)[w] \} = 0).
      { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
        apply AxiomII in H18 as []. destruct (classic (z ∈ ω)).
        - pose proof H20. rewrite <-H9 in H20; rewrite <-H11 in H21.
          apply Property_Value,Property_ran in H20;
          apply Property_Value,Property_ran in H21; auto.
          rewrite H12 in H21. rewrite H10 in H20.
          pose proof in_ω_0; pose proof in_ω_1.
          apply MKT41 in H20; apply MKT41 in H21; eauto.
          rewrite H20,H21 in H19. elim (@ MKT16 1); auto.
        - rewrite <-H11 in H20. apply MKT69a in H20.
          rewrite H20 in H19. elim MKT39; eauto. }
      rewrite H18 in H15. destruct H as [_[]].
      apply AxiomII in H as [H[[H20[]]]]; auto.
    + pose proof H4. apply AxiomII in H16 as [H16[f[H17[H18[]]]]].
      assert ((Const 0)〈F0〉 = F 0)%n'.
      { apply F_Const_Fa; destruct H as [_[]]; auto; apply in_ω_0. }
      rewrite H20,<-H21 in H15. apply N'_Ord_Instantiate in H15; auto.
      assert (\{ λ w, f[w] ∈ (Const 0)[w] \} = 0).
      { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
        apply AxiomII in H22 as []. destruct (classic (z ∈ ω)).
        - rewrite <-H9 in H24. apply Property_Value,Property_ran
          in H24; auto. rewrite H10 in H24.
          apply MKT41 in H24; pose proof in_ω_0; eauto.
          rewrite H24 in H23. elim (@ MKT16 (f[z])); auto.
        - rewrite <-H18 in H24. apply MKT69a in H24.
          rewrite H24 in H23. elim MKT39; eauto. }
      rewrite H22 in H15. destruct H as [_[]].
      apply AxiomII in H as [H[[H24[]]]]; auto.
    + rewrite H15 in H5. rewrite (N'_Plus_Commutation (F 1))
      in H5; auto. apply N'_Plus_Cancellation in H5; auto.
      rewrite H5 in H15. elim N'0_isnot_N'1; auto.
Qed.

(* 以下5条定义及结论旨在说明*N与*Z_*N是同构的. *)
(* 构造: φ1是*N到*Z_*N的一一函数*)
Definition φ1 := \{\ λ u v, u ∈ N' /\ v = \[[u,(F 0)]\] \}\.

Property φ1_is_Function : Function1_1 φ1 /\ dom(φ1) = N' /\ ran(φ1) = Z'_N'.
Proof.
  intros. assert (Function1_1 φ1).
  { repeat split; unfold Relation; intros; try destruct H.
    - apply AxiomII in H as [H[x[y[]]]]; eauto.
    - apply AxiomII' in H as [H[]].
      apply AxiomII' in H0 as [H0[]]. rewrite H2,H4; auto.
    - apply AxiomII in H as [H[x[y[]]]]; eauto.
    - apply AxiomII' in H as []. apply AxiomII' in H1 as [H1[]].
      apply AxiomII' in H0 as []. apply AxiomII' in H4 as [H4[]].
      rewrite H3 in H6. pose proof in_ω_0. apply Fn_in_N' in H7.
      apply R_N'_Property in H6; try split; auto.
      rewrite N'_Plus_Commutation in H6; try split; auto.
      apply N'_Plus_Cancellation in H6; try split; auto. }
  split; auto. destruct H. split; apply AxiomI; split; intros.
  - apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2; tauto.
  - apply AxiomII; split; eauto. exists (\[[z,(F 0)]\]).
    apply AxiomII'; split; auto. apply MKT49a; eauto. apply (MKT33 N'×N').
    apply MKT74; apply N'_is_Set; destruct H; auto.
    unfold Included; intros. apply AxiomII in H2; tauto.
  - apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2 as [H2[]].
    apply AxiomII; split; eauto.
  - apply AxiomII in H1 as [H1[x[]]]. apply AxiomII; split; auto.
    exists x. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Property φ1_N'0 : φ1[F 0] = Z'0.
Proof.
  intros. destruct φ1_is_Function as [[][]].
  assert ((F 0) ∈ N').
  { apply Fn_in_N',in_ω_0; destruct H; auto. }
  rewrite <-H1 in H3. apply Property_Value,AxiomII' in H3 as [_[_]]; auto.
  rewrite Z'0_Property; auto.
Qed.

Property φ1_N'1 : φ1[F 1] = Z'1.
Proof.
  intros. destruct φ1_is_Function as [[][]].
  assert ((F 1) ∈ N').
  { apply Fn_in_N',in_ω_1; destruct H; auto. }
  rewrite <-H1 in H3. apply Property_Value,AxiomII' in H3 as [_[_]]; auto.
  rewrite Z'1_Property; auto.
Qed.

(* φ1是序保持的:
   *Z_*N中元素的排序方式类似于*N中元素的排序方式.  *)
Property φ1_PrOrder : ∀ m n, m ∈ N' -> n ∈ N'
  -> (m < n)%n' <-> φ1[m] < φ1[n].
Proof.
  intros. destruct φ1_is_Function as [[][]].
  assert ((F 0) ∈ N').
  { pose proof in_ω_0. apply Fn_in_N' in H5; auto. }
  assert (φ1[m] = \[[m,(F 0)]\] /\ Ensemble (φ1[m])) as [].
  { rewrite <-H3 in H. apply Property_Value in H; auto.
    apply AxiomII' in H as [H[]]. split; auto. apply MKT49b in H; tauto. }
  assert (φ1[n] = \[[n,(F 0)]\] /\ Ensemble (φ1[n])) as [].
  { rewrite <-H3 in H0. apply Property_Value in H0; auto.
    apply AxiomII' in H0 as [H0[]]. split; auto. apply MKT49b in H0; tauto. }
  split; intros.
  - apply AxiomII'; split. apply MKT49a; auto. intros.
    rewrite H6 in H15; rewrite H8 in H16.
    apply R_N'_Property in H15; apply R_N'_Property in H16; auto.
    rewrite (N'_Plus_Commutation _ m0),N'_Plus_Property in H15;
    rewrite (N'_Plus_Commutation _ p),N'_Plus_Property in H16; auto.
    assert (((n0 + q) + m) < ((n0 + q) + n))%n'.
    { apply N'_Plus_PrOrder; try apply N'_Plus_in_N'; auto. }
    rewrite N'_Plus_Association,N'_Plus_Association,
    (N'_Plus_Commutation q),<-(N'_Plus_Association n0),
    (N'_Plus_Commutation n0),(N'_Plus_Commutation q),H15,H16 in H17; auto.
  - apply AxiomII' in H10 as [].
    assert ((m + (F 0)) < ((F 0) + n))%n'. { apply H11; auto. }
    rewrite N'_Plus_Commutation in H12; auto.
    apply N'_Plus_PrOrder in H12; auto.
Qed.

(* φ1是加法保持的. *)
Property φ1_PrPlus : ∀ m n, m ∈ N' -> n ∈ N' -> φ1[(m + n)%n'] = φ1[m] + φ1[n].
Proof.
  intros. destruct φ1_is_Function as [[][]].
  assert ((m + n)%n' ∈ N'). { apply N'_Plus_in_N'; auto. }
  rewrite <-H3 in H5,H,H0. apply Property_Value in H5;
  apply Property_Value in H; apply Property_Value in H0; auto.
  apply AxiomII' in H as [H[]]. apply AxiomII' in H0 as [H0[]].
  apply AxiomII' in H5 as [H5[]]. rewrite H7,H9,H11.
  clear H7 H9 H11. rewrite Z'_Plus_Instantiate; auto;
  try apply Fn_in_N'; try apply in_ω_0; destruct H; auto.
  rewrite N'_Plus_Property; auto; try apply Fn_in_N';
  try apply in_ω_0; try split; auto.
Qed.

(* φ1是乘法保持的 *)
Property φ1_PrMult : ∀ m n, m ∈ N' -> n ∈ N' -> φ1[(m · n)%n'] = φ1[m] · φ1[n].
Proof.
  intros. destruct φ1_is_Function as [[][]].
  assert ((m · n)%n' ∈ N'). { apply N'_Mult_in_N'; auto. }
  rewrite <-H3 in H5,H,H0. apply Property_Value in H5;
  apply Property_Value in H; apply Property_Value in H0; auto.
  apply AxiomII' in H as [H[]]. apply AxiomII' in H0 as [H0[]].
  apply AxiomII' in H5 as [H5[]]. rewrite H7,H9,H11.
  clear H7 H9 H11. rewrite Z'_Mult_Instantiate; auto;
  try apply Fn_in_N'; try apply in_ω_0; destruct H; auto.
  rewrite (N'_Mult_Commutation (F 0) n),N'_Mult_Property1,
  N'_Mult_Property1,N'_Mult_Property1,N'_Plus_Property,
  N'_Plus_Property; try split; auto; apply Fn_in_N';
  try apply in_ω_0; auto.
Qed.

(* 关于 *Z_*N 的一些性质 *)
Property Z'_N'_Property1 : Z' ~ Z'_N'
  = \{ λ u, ∃ m, m ∈ N' /\ m <> F 0 /\ u = \[[(F 0),m]\] \}.
Proof.
  pose proof in_ω_0; pose proof H. apply Fn_in_N' in H0; auto.
  apply AxiomI; split; intros.
  - apply MKT4' in H1 as []. apply AxiomII; split; eauto.
    apply AxiomII in H1 as [H1[x[]]].
    apply AxiomII in H3 as [H3[m[n[H5[]]]]]. rewrite H4,H5 in *.
    assert (m ∈ N' /\ n ∈ N') as []; auto.
    apply (N'_Ord_Tri m n) in H8 as []; auto; clear H9.
    + apply N'_Plus_PrOrder_Corollary in H8 as [a[[H8[]]]]; auto.
      exists a. repeat split; auto. intro. rewrite <-H12 in H9.
      elim (N'_Ord_irReflex a a); auto.
      apply R_N'_Property; auto. rewrite N'_Plus_Property; auto.
    + apply AxiomII in H2 as []. elim H9.
      apply AxiomII; split; auto. destruct H8.
      * apply N'_Plus_PrOrder_Corollary in H8 as [a[[H8[]]]]; auto.
        exists a. split; auto. apply R_N'_Property; auto.
        rewrite N'_Plus_Property; auto.
      * exists (F 0). split; auto. apply R_N'_Property; auto.
        rewrite N'_Plus_Property,N'_Plus_Property; auto.
  - apply AxiomII in H1 as [H1[n[H2[]]]]. apply MKT4'; split.
    + apply AxiomII; split; auto. exists ([F 0,n]). split; auto.
      apply AxiomII'; split; auto. apply MKT49a; eauto.
    + apply AxiomII; split; auto. intro.
      apply AxiomII in H5 as [H5[x[]]].
      rewrite H4 in H7. apply R_N'_Property in H7; auto.
      rewrite N'_Plus_Property in H7; auto.
      assert ((F 0) ∈ N' /\ n ∈ N') as []; auto.
      apply (N'_Ord_Tri _ n) in H8 as [H8|[|]]; auto;
      clear H9; elim (N'0_is_FirstMember n); auto.
      assert (((F 0) ∈ N' /\ x ∈ N')) as []; auto.
      apply (N'_Ord_Tri _ x) in H9 as [H9|[|]]; auto;
      clear H10; elim (N'0_is_FirstMember x); auto.
      * apply (N'_Plus_PrOrder _ _ n) in H9; auto.
        apply (N'_Plus_PrOrder _ _ (F 0)) in H8; auto.
        rewrite N'_Plus_Property,N'_Plus_Commutation in H8; auto.
        apply (N'_Ord_Trans (F 0)) in H9; try apply N'_Plus_in_N'; auto.
        rewrite <-H7 in H9. elim (N'_Ord_irReflex_weak (F 0)); auto.
      * rewrite H7,<-H9,N'_Plus_Property in H8; auto.
        elim (N'_Ord_irReflex n n); auto.
Qed.

Property Z'_N'_Property2 : ∀ u, u ∈ Z' -> u ∈ (Z' ~ Z'_N') <-> u < Z'0.
Proof.
  intros. pose proof in_ω_0; pose proof H0.
  apply Fn_in_N' in H1. pose proof H as Ha.
  apply AxiomII in H as [H[x[]]]. apply AxiomII in H2 as [H2[m[n[H4[]]]]].
  rewrite H3,H4 in *. split; intros.
  - apply MKT4' in H7 as []. apply AxiomII in H8 as [].
    rewrite Z'0_Property; auto. apply Z'_Ord_Instantiate; auto.
    rewrite N'_Plus_Property,N'_Plus_Property; auto.
    assert (m ∈ N' /\ n ∈ N') as []; auto.
    apply (N'_Ord_Tri m n) in H10 as []; auto; clear H11.
    elim H9. apply AxiomII; split; auto. destruct H10.
    + apply N'_Plus_PrOrder_Corollary in H10 as [a[[H10[]]]]; auto.
      exists a. split; auto. apply R_N'_Property; auto.
      rewrite N'_Plus_Property; auto.
    + exists (F 0). split; auto. apply R_N'_Property; auto.
      rewrite N'_Plus_Property,N'_Plus_Property; auto.
  - apply MKT4'; split; auto. apply AxiomII; split; auto.
    intro. rewrite Z'0_Property in H7; auto.
    apply Z'_Ord_Instantiate in H7; auto.
    rewrite N'_Plus_Property,N'_Plus_Property in H7; auto.
    apply AxiomII in H8 as [H8[a[]]]. apply R_N'_Property in H10; auto.
    rewrite N'_Plus_Property in H10; auto. rewrite H10 in H7.
    assert ((n + a) < (n + (F 0)))%n'. { rewrite N'_Plus_Property; auto. }
    apply N'_Plus_PrOrder in H11; auto. elim (N'0_is_FirstMember a); auto.
Qed.

Property Z'_N'_Property3 : ∀ u, u ∈ (Z'_N' ~ [Z'0])
  -> ∃! u0, u0 ∈ (Z' ~ Z'_N') /\ u + u0 = Z'0.
Proof.
  intros. assert (u ∈ Z').
  { apply MKT4' in H as []. apply Z'_N'_propersubset_Z'; auto. }
  assert ((F 0) ∈ N'). { apply Fn_in_N',in_ω_0; auto. }
  assert (Z'0 < u).
  { apply MKT4' in H as []. apply AxiomII in H as [_[m[]]].
    rewrite H3,Z'0_Property; auto. apply Z'_Ord_Instantiate; auto.
    rewrite N'_Plus_Property,N'_Plus_Commutation,N'_Plus_Property; auto.
    pose proof H. apply N'0_is_FirstMember in H; auto.
    pose proof H1. apply (N'_Ord_Tri _ m) in H5 as [H5|[|]]; auto.
    elim H; auto. rewrite H3,<-H5,<-Z'0_Property in H2; auto.
    apply AxiomII in H2 as []. elim H6. apply MKT41; auto. }
  pose proof H0. apply Z'_Neg in H3 as [u0[[]]]; auto.
  exists u0. repeat split; auto. rewrite Z'_N'_Property1; auto.
  - apply AxiomII; split; eauto. apply MKT4' in H as [].
    apply AxiomII in H as [_[m[]]]. exists m. repeat split; auto.
    intro. rewrite H7,H8,<-Z'0_Property in H2; auto.
    elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'.
    apply Z'_Neg_Instantiate; auto. rewrite <-H7; auto.
  - intros u1 []. rewrite <-H4 in H7. apply Z'_Plus_Cancellation in H7; auto.
    apply MKT4' in H6; tauto.
Qed.

Property Z'_N'_Property4 : ∀ u, u ∈ (Z' ~ Z'_N')
  -> ∃! u0, u0 ∈ (Z'_N' ~ [Z'0]) /\ u + u0 = Z'0.
Proof.
  intros. assert (u ∈ Z'). { apply MKT4' in H; tauto. }
  assert ((F 0) ∈ N'). { apply Fn_in_N',in_ω_0; auto. }
  assert (u < Z'0).
  { rewrite Z'_N'_Property1 in H; auto.
    apply AxiomII in H as [_[m[H[]]]]. pose proof H.
    apply N'0_is_FirstMember in H4; auto. pose proof H1.
    apply (N'_Ord_Tri _ m) in H5 as [H5|[|]]; auto.
    rewrite H3,Z'0_Property; auto. apply Z'_Ord_Instantiate; auto.
    rewrite N'_Plus_Property,N'_Plus_Property; auto.
    elim H4; auto. elim H2; auto. }
  pose proof H0. apply Z'_Neg in H3 as [u0[[]]]; auto.
  exists u0. repeat split; auto.
  - apply MKT4'; split. apply AxiomII; split; eauto.
    rewrite Z'_N'_Property1 in H; auto.
    apply AxiomII in H as [_[m[H[]]]]. exists m. split; auto.
    apply Z'_Neg_Instantiate; auto. rewrite <-H7; auto.
    apply AxiomII; split; eauto. intro. apply MKT41 in H6.
    rewrite H6,Z'_Plus_Property in H4; auto. rewrite <-H4 in H2.
    elim (Z'_Ord_irReflex u u); auto. eauto with Z'.
  - intros u1 []. rewrite <-H4 in H7.
    apply Z'_Plus_Cancellation in H7; auto.
    apply MKT4' in H6 as []. apply Z'_N'_propersubset_Z'; auto.
Qed.

(* *Z_Z是由*N_N(主超滤集)以*N×*N上的等价关系扩张而来.
   这里的主超滤集实际上可以作为自然数集使用; *Z_Z可作为一般整数集使用. *)
Definition Z'_Z := \{ λ u, ∃ m n, m ∈ N'_N /\ n ∈ N'_N /\ u = \[[m,n]\] \}.

Property Z'_Z_subset_Z' : Z'_Z ⊂ Z'.
Proof.
  intros. unfold Included; intros. apply AxiomII in H as [H[m[n[H0[]]]]].
  apply AxiomII; split; auto. exists [m,n]. split; auto. apply AxiomII'; split.
  apply MKT49a; eauto. split; apply N'_N_subset_N'; auto.
Qed.

Property Z'_Z_is_Set : Ensemble Z'_Z.
Proof.
  intros. apply (MKT33 Z'); [apply Z'_is_Set|apply Z'_Z_subset_Z'].
Qed.

Property Z'0_in_Z'_Z : Z'0 ∈ Z'_Z.
Proof.
  intros. apply AxiomII; split; eauto with Z'.
  exists (F 0),(F 0). repeat split; try apply Fn_in_N'_N; auto.
  rewrite Z'0_Property; auto.
Qed.

Property Z'1_in_Z'_Z : Z'1 ∈ Z'_Z.
Proof.
  intros. apply AxiomII; split; eauto with Z'.
  exists (F 1),(F 0). repeat split; try apply Fn_in_N'_N; auto.
  apply in_ω_1. rewrite Z'1_Property; auto.
Qed.

(* *Z_Z对加法封闭. *)
Property Z'_Z_Plus_in_Z'_Z : ∀ u v, u ∈ Z'_Z -> v ∈ Z'_Z -> (u + v) ∈ Z'_Z.
Proof.
  intros. pose proof H; pose proof H0.
  apply Z'_Z_subset_Z' in H1; apply Z'_Z_subset_Z' in H2; auto.
  pose proof H1. apply (Z'_Plus_in_Z' u v) in H3; auto.
  apply AxiomII; split; eauto.
  apply AxiomII in H as [H[x[x1[H4[]]]]].
  apply AxiomII in H0 as [H0[y[y1[H7[]]]]].
  exists (x + y)%n',(x1 + y1)%n'.
  rewrite H6,H9,Z'_Plus_Instantiate; try apply N'_N_subset_N'; auto.
  repeat split; try apply N'_N_Plus_in_N'_N; auto.
Qed.

(* *Z_Z对乘法封闭.*)
Property Z'_Z_Mult_in_Z'_Z : ∀ u v, u ∈ Z'_Z -> v ∈ Z'_Z -> (u · v) ∈ Z'_Z.
Proof.
  intros. pose proof H; pose proof H0.
  apply Z'_Z_subset_Z' in H1; apply Z'_Z_subset_Z' in H2; auto.
  pose proof H1. apply (Z'_Mult_in_Z' u v) in H3; auto.
  apply AxiomII; split; eauto.
  apply AxiomII in H as [H[x[x1[H4[]]]]].
  apply AxiomII in H0 as [H0[y[y1[H7[]]]]].
  exists ((x · y) + (x1 · y1))%n', ((x · y1) + (x1 · y))%n'.
  rewrite H6,H9,Z'_Mult_Instantiate; try apply N'_N_subset_N'; auto.
  repeat split; try apply N'_N_Plus_in_N'_N; try apply N'_N_Mult_in_N'_N; auto.
Qed.

(* *Z_Z是*Z的真子集. *)
Property Z'_Z_propersubset_Z' : Z'_Z ⊂ Z' /\ Z'_Z <> Z'.
Proof.
  destruct NPAUF. split. apply Z'_Z_subset_Z'; auto. intro.
  pose proof N'_N_propersubset_N' as [].
  assert ((N' ~ N'_N) <> Φ).
  { intro. elim H3. apply AxiomI; split; intros; auto.
    apply NNPP; intro. assert (z ∈ (N' ~ N'_N)).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto. }
    rewrite H4 in H7. elim (@ MKT16 z); auto. }
  apply NEexE in H4 as [t]. apply MKT4' in H4 as [].
  apply AxiomII in H5 as [].
  assert ((F 0) ∈ N').
  { pose proof in_ω_0. apply Fn_in_N' in H7; auto. }
  assert (\[[t,(F 0)]\] ∈ Z'). { apply Z'_Instantiate2; auto. }
  rewrite <-H1 in H8. apply AxiomII in H8 as [H8[x[y[H9[]]]]].
  apply R_N'_Property in H11; auto.
  rewrite (N'_Plus_Commutation _ x),N'_Plus_Property in H11; auto.
  pose proof H9; pose proof H10. apply N'_N_subset_N' in H12,H13.
  assert (t ∈ (N' ~ N'_N)).
  { apply MKT4'; split; auto. apply AxiomII; auto. }
  apply AxiomII in H9 as [H9[m[]]].
  apply AxiomII in H10 as [H10[n[]]].
  assert ((F 0) < t)%n'. { apply N'_Infty,Fn_in_N'_N; auto. }
  assert (y ∈ N' /\ x ∈ N') as []; auto.
  apply (N'_Ord_Tri y x) in H20 as []; auto; clear H21.
  - assert (x < t)%n'. { rewrite H16. apply N'_Infty,Fn_in_N'_N; auto. }
    apply (N'_Plus_PrOrder _ _ y) in H21; auto.
    rewrite (N'_Plus_Commutation y t),H11 in H21; auto.
    assert ((x + y) < (x + (F 0)))%n'.
    { rewrite N'_Plus_Property,N'_Plus_Commutation; auto. }
    apply N'_Plus_PrOrder in H22; auto. rewrite H18 in H22.
    pose proof H. pose proof φ_is_Function as [[][]].
    pose proof in_ω_0. rewrite <-H26 in H17,H28.
    apply Property_Value in H17; apply Property_Value in H28; auto.
    apply AxiomII' in H17 as [_[]]. apply AxiomII' in H28 as [_[]].
    rewrite <-H29,<-H30 in H22. apply φ_PrOrder in H22; auto.
    elim (@ MKT16 n); auto.
  - apply (N'_Plus_PrOrder _ _ y) in H19; auto.
    rewrite N'_Plus_Property,N'_Plus_Commutation,H11 in H19; auto.
    destruct H20. apply (N'_Ord_Trans y) in H20; auto.
    elim (N'_Ord_irReflex y y); auto. rewrite H20 in H19.
    elim (N'_Ord_irReflex x x); auto.
Qed.

(* 关于*Z中无穷大的性质 *)
(* 两个引理 *)
Lemma Z'_Infty_Lemma1 : φ1「N'_N」 = \{ λ u, u ∈ Z'_Z /\ (Z'0 = u \/ Z'0 < u) \}.
Proof.
  destruct φ1_is_Function as [[][]].
  assert ((F 0) ∈ N'_N). { apply Fn_in_N'_N,in_ω_0; auto. }
  pose proof H3. apply N'_N_subset_N' in H4; auto.
  apply AxiomI; split; intros.
  - apply AxiomII in H5 as [H5[m[]]].
    apply AxiomII; repeat split; eauto.
    + apply AxiomII; split; eauto. pose proof H7.
      apply N'_N_subset_N' in H8; auto. rewrite <-H1 in H8.
      apply Property_Value in H8; auto. apply AxiomII' in H8 as [_[_]].
      exists m,(F 0). rewrite H6. repeat split; auto.
    + apply N'_N_subset_N' in H7; auto. pose proof H4.
      apply (N'_Ord_Tri _ m) in H8 as [H8|[|]]; auto.
      * apply φ1_PrOrder in H8; auto. rewrite <-H6,φ1_N'0 in H8; auto.
      * apply N'0_is_FirstMember in H7; elim H7; auto.
      * rewrite <-H8,φ1_N'0 in H6; auto.
  - apply AxiomII in H5 as [_[]]. apply AxiomII; split; eauto. destruct H6.
    + exists (F 0). split; auto. rewrite φ1_N'0; auto.
    + apply AxiomII in H5 as [_[m[n[H5[]]]]]. rewrite H8,Z'0_Property in H6; auto.
      pose proof H5; pose proof H7. apply N'_N_subset_N' in H9,H10; auto.
      apply Z'_Ord_Instantiate in H6; auto.
      rewrite N'_Plus_Commutation,N'_Plus_Property,N'_Plus_Commutation,
      N'_Plus_Property in H6; auto.
      apply N'_Plus_PrOrder_Corollary in H6 as [x[[H6[]]_]]; auto.
      exists x. split.
      * rewrite <-H1 in H6. apply Property_Value,AxiomII' in H6 as [_[]]; auto.
        rewrite H8,H13. apply R_N'_Property; auto. rewrite N'_Plus_Property; auto.
      * destruct NPAUF as [_]. apply NNPP; intro.
        assert (x ∈ (N' ~ N'_N)).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto. }
        apply AxiomII in H5 as [_[a[]]]. apply (N'_Infty x (F a)) in H15; auto.
        rewrite <-H16,<-H12 in H15. pose proof H10.
        apply N'0_is_FirstMember in H10; auto. elim H10.
        apply (N'_Plus_PrOrder _ _ x); auto.
        rewrite N'_Plus_Property,N'_Plus_Commutation; auto.
        apply Fn_in_N'_N; auto.
Qed.

Lemma Z'_Infty_Lemma2 : φ1「(N' ~ N'_N)」 = \{ λ u, u ∈ (Z' ~ Z'_Z) /\ Z'0 < u \}.
Proof.
  destruct φ1_is_Function as [[][]].
  assert ((F 0) ∈ N'_N). { apply Fn_in_N'_N,in_ω_0; auto. }
  pose proof H3. apply N'_N_subset_N' in H4; auto. apply AxiomI; split; intros.
  - apply AxiomII in H5 as [H5[m[]]]. apply AxiomII; repeat split; eauto.
    + apply MKT4'; split.
      * apply MKT4' in H7 as []. rewrite <-H1 in H7.
        apply Property_Value,Property_ran in H7; auto. rewrite H2 in H7.
        apply Z'_N'_propersubset_Z'; auto. rewrite H6; auto.
      * apply AxiomII; split; eauto. intro. pose proof H8.
        apply Z'_Z_subset_Z' in H9; auto. pose proof Z'0_in_Z'.
        pose proof H10. apply (Z'_Ord_Tri z) in H11 as [H11|]; auto.
        -- rewrite H6,<-φ1_N'0 in H11; auto. apply MKT4' in H7 as [].
           apply φ1_PrOrder in H11; auto. apply N'0_is_FirstMember in H7; auto.
        -- assert (z ∈ φ1「N'_N」).
           { rewrite Z'_Infty_Lemma1; auto.
             apply AxiomII; repeat split; eauto. destruct H11; auto. }
           apply AxiomII in H12 as [_[x[]]]. rewrite H6 in H12.
           apply MKT4' in H7 as []. apply f11inj in H12; try rewrite H1; auto;
           try apply N'_N_subset_N'; auto; subst.
           apply AxiomII in H14 as [_]; auto.
    + destruct NPAUF as [_]. pose proof H7. apply MKT4' in H7 as [H7 _].
        apply (N'_Infty m (F 0)) in H9; auto. apply φ1_PrOrder in H9; auto.
        rewrite <-φ1_N'0,H6; auto.
  - apply AxiomII in H5 as [H5[]]. apply AxiomII; split; auto.
    assert (z ∈ Z'_N').
    { apply NNPP; intro. assert (z ∈ (Z' ~ Z'_N')).
      { apply MKT4' in H6 as []. apply MKT4'; split; auto.
        apply AxiomII; split; auto. }
      rewrite Z'_N'_Property1 in H9; auto. apply AxiomII in H9 as [_[x[H9[]]]].
      rewrite Z'0_Property,H11 in H7; auto. apply Z'_Ord_Instantiate in H7; auto.
      rewrite N'_Plus_Property,N'_Plus_Commutation,N'_Plus_Property in H7; auto.
      apply N'0_is_FirstMember in H9; auto. }
    pose proof H8. rewrite <-H2 in H9. apply Einr in H9 as [x[]]; auto.
    exists x. split; auto. apply MKT4'; split. rewrite <-H1; auto.
    apply AxiomII; split; eauto. intro.
    apply Property_Value,AxiomII' in H9 as [_[]]; auto.
    apply MKT4' in H6 as []. apply AxiomII in H13 as [_].
    elim H13. apply AxiomII; split; auto. rewrite H10; eauto.
Qed.

Property Z'_infinity : ∀ u t, u ∈ Z'_Z -> t ∈ (Z' ~ Z'_Z) -> t < u \/ u < t.
Proof.
  destruct NPAUF. intros. destruct φ1_is_Function as [[][]].
  pose proof Z'0_in_Z'. assert (t ∈ Z'). { apply MKT4' in H2; tauto. }
  assert ((F 0) ∈ N'). { apply Fn_in_N',in_ω_0; auto. }
  pose proof Z'_Infty_Lemma1. pose proof Z'_Infty_Lemma2.
  assert (∀ t0 u0, t0 ∈ (Z' ~ Z'_Z) -> u0 ∈ Z'_Z -> Z'0 < t0 -> Z'0 < u0
   -> u0 < t0).
  { intros. assert (t0 ∈ φ1「(N' ~ N'_N)」).
    { rewrite H11. apply AxiomII; split; eauto. }
    apply AxiomII in H16 as [_[m[]]].
    assert (u0 ∈ φ1「N'_N」).
    { rewrite H10. apply AxiomII; repeat split; eauto. }
    apply AxiomII in H18 as [_[n[]]].
    apply AxiomII in H19 as [_[x[]]]. pose proof H17.
    apply (N'_Infty m (F x)) in H17; auto. rewrite <-H20 in H17.
    apply φ1_PrOrder in H17; auto. rewrite H18,H16; auto.
    rewrite H20. apply Fn_in_N'; destruct H; auto. apply MKT4' in H21; tauto.
    apply Fn_in_N'_N; auto. }
  pose proof H1. apply Z'_Z_propersubset_Z' in H13; auto.
  pose proof H7. apply (Z'_Ord_Tri t) in H14 as [H14|[|]]; auto.
  - pose proof H7. apply (Z'_Ord_Tri u) in H15 as [H15|[|]]; auto.
    + apply Z'_Plus_PrOrder_Corollary in H14 as [t0[[H14[]]_]]; auto.
      apply Z'_Plus_PrOrder_Corollary in H15 as [u0[[H15[]]_]]; auto.
      assert (u0 < t0).
      { apply H12; auto.
        - apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
          apply MKT4' in H2 as []. apply AxiomII in H21 as []. elim H22.
          apply AxiomII in H20 as [_[m[n[H20[]]]]].
          rewrite Z'_Plus_Commutation,H24 in H17; auto.
          apply Z'_Neg_Instantiate in H17; try apply N'_N_subset_N'; auto.
          apply AxiomII; split; eauto.
        - apply AxiomII in H1 as [_[m[n[H1[]]]]]. rewrite H21 in H19.
          apply Z'_Neg_Instantiate in H19; try apply N'_N_subset_N'; auto.
          apply AxiomII; split; eauto. }
      apply (Z'_Plus_PrOrder _ _ t) in H20; auto. rewrite H17 in H20.
      apply (Z'_Plus_PrOrder _ _ u) in H20; auto with Z'.
      rewrite Z'_Plus_Property,(Z'_Plus_Commutation t),<-Z'_Plus_Association,H19,
      Z'_Plus_Commutation,Z'_Plus_Property in H20; auto.
    + apply (Z'_Ord_Trans t) in H15; auto.
    + rewrite <-H15 in H14; auto.
  - pose proof H7. apply (Z'_Ord_Tri u) in H15 as [H15|[|]]; auto.
    + apply (Z'_Ord_Trans _ _ t) in H15; auto.
    + rewrite <-H15 in H14; auto.
  - apply MKT4' in H2 as []. apply AxiomII in H15 as [_].
    elim H15. rewrite Z'0_Property in H14; auto.
    apply AxiomII; split; eauto. exists (F 0),(F 0).
    repeat split; auto; apply Fn_in_N'_N; destruct H; auto.
Qed.



