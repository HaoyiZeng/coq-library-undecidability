Require Import Coq.Arith.Cantor Coq.Arith.PeanoNat Lia Vector Arith.Compare_dec List.
Require Import Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Import ListNotations.
Notation vec := t.
Notation "'Σ' x .. y , p" :=
    (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
    format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
: type_scope.

Section property.

    Context {X Y: Type}.
    Variable R: X -> X -> Prop.
    Variable R_bi: X -> Y -> Prop.
    Variable R_tr: X -> X -> X -> Prop.

    Definition total := forall x, exists y, R_bi x y.
    Definition trans := forall x y z, R x y -> R y z -> R x z.
    Definition total_tr := forall x y, exists z, R_tr x y z.
    Definition direct := forall x y, exists z, R_bi x z /\ R_bi y z.

    Definition function_rel' := forall x, exists! y, R_bi x y.

    Definition consf (f: Y -> X) := fun x y => R (f x) (f y).

End property.


Notation "R ∘ f" := (consf R f) (at level 30).

Section axiom.

    Implicit Type (X: Type).

    Definition DC_on X :=
        forall (R: X -> X -> Prop) , X -> total R ->
            exists f: nat -> X, forall n, R (f n) (f (S n)).

    Definition DC_root_on X (R: X -> X -> Prop) := 
        total R -> forall x: X,
            exists f: nat -> X, f 0 = x /\ forall n, R (f n) (f (S n)).

    Definition BCC_on X := forall (R: nat -> X -> Prop),
        X -> total R -> exists f: nat -> X, forall n, exists m, R n (f m).

    Definition BDC_on A := forall R : A -> A -> Prop, 
        A -> (forall x, exists y, R x y) -> 
            exists f : nat -> A, total (R ∘ f).

    Definition BDC2_on X := forall R: X -> X -> X -> Prop,
        X -> total_tr R -> 
        exists f: nat -> X, forall x y, exists z, R (f x) (f y) (f z).

    Definition OBDC_on X := forall R: X -> X -> X -> Prop,
        X -> exists f: nat -> X, 
            total_tr R <-> forall x y, exists z, R (f x) (f y) (f z).

    Definition CC_on X := forall R: nat -> X -> Prop,
        X -> total R ->
            exists f: nat -> X, forall n, R n (f n).

    Definition BDP_on X := forall (P: X -> Prop),
        X -> exists f: nat -> X,
            (forall n, P (f n)) -> (forall x, P x).

    Definition BEP_on X := forall (P: X -> Prop),
        X -> exists f: nat -> X,
            (exists x, P x) -> (exists n, P (f n)).

    Definition DDC_on X := forall (R: X -> X -> Prop),
        X -> trans R -> direct R ->
            exists f: nat -> X, direct (R ∘ f).

    Definition PDC_root_on X (R: X -> X -> Prop) :=
        (forall x, exists y, R x y) -> forall w,
            exists f : nat -> X -> Prop, function_rel' f /\ f 0 w /\ forall n, exists x y, f n x /\ f (S n) y /\ R x y.

    Definition DC := forall X, DC_on X.
    Definition DC_root := forall X (R: X -> X -> Prop), DC_root_on R.
    Definition PDC_root := forall X (R: X -> X -> Prop), PDC_root_on R.
    Definition BCC := forall X, BCC_on X.
    Definition BDC := forall X, BDC_on X.
    Definition BDC2 := forall X, BDC2_on X.
    Definition OBDC := forall X, OBDC_on X.
    Definition CC := forall X, CC_on X.
    Definition AC00 := CC_on nat.
    Definition BDP := forall X, BDP_on X.
    Definition BEP := forall X, BEP_on X.
    Definition DDC := forall X, DDC_on X.

End axiom.

Section BDC_BCC.

Definition BDC_root:=
  forall A (R : A -> A -> Prop), 
        forall a: A, (forall x, exists y, R x y) ->
            exists f : nat -> A, f 0 = a /\ forall x, exists y, R (f x) (f y).

Inductive reachable {X} (R : X -> X -> Prop) x0 x : Prop :=
    | base : R x0 x -> reachable R x0 x
    | step y : reachable R x0 y -> R y x -> reachable R x0 x.

Definition reachable' {X} (R : X -> X -> Prop) x0 x :=
    exists f : nat -> X, exists N, f 0 = x0 /\ f (S N) = x /\ forall n, n <= N -> R (f n) (f (S n)).
    

Lemma reach_reach' {X} (R : X -> X -> Prop) x0 x :
    reachable R x0 x -> reachable' R x0 x.
Proof.
    induction 1.
    - exists (fun n => match n with 0 => x0 | _ => x end), 0. split; trivial. split; trivial.
        intros n. inversion 1; subst. apply H.
    - destruct IHreachable as (f & N & H1 & H2 & H3).
        exists (fun n => if PeanoNat.Nat.leb n (S N) then f n else x), (S N). split. 2: split.
        + rewrite Compare_dec.leb_correct; try lia. apply H1.
        + rewrite Compare_dec.leb_correct_conv; try lia. reflexivity.
        + intros n HN. assert (n <= N \/ n = S N) as [Hn| ->] by lia.
        * rewrite ?Compare_dec.leb_correct; try lia. now apply H3.
        * rewrite Compare_dec.leb_correct, Compare_dec.leb_correct_conv; try lia. now rewrite H2.
Qed.

Lemma BDC_impl_BDC_root:
    BDC -> BDC_root .
Proof.
    intros dc A R w total_R.
    destruct (total_R w) as [y0 Hy0]. 
    pose (a0 := exist _ y0 (@base _ R _ _ Hy0)).
    destruct (dc { x | reachable R w x } (fun a b => R (proj1_sig a) (proj1_sig b)) ) as [f Hf].
    - easy.
    - intros [x Hx]. destruct (total_R x) as [y Hy]. exists (exist _ y (@step _ R w y x Hx Hy)). apply Hy.
    - destruct (f 0) as [x Hx] eqn : H0.
      destruct (@reach_reach' _ _ _ _ Hx) as (g & N & H1 & H2 & H3).
      exists (fun n => if PeanoNat.Nat.leb n N then g n else proj1_sig (f (n - N - 1))). split.
      + cbn. apply H1.
      + intros n. assert (n <= N \/ n > N) as [Hn|Hn] by lia.
        * assert (S n <= N \/ n = N) as [Hn'| ->] by lia. 
          -- exists (S n). rewrite ?Compare_dec.leb_correct; try lia. now apply H3.
          -- exists (S N). rewrite Compare_dec.leb_correct, Compare_dec.leb_correct_conv; try lia.
             assert (S N - N - 1 = 0) as -> by lia. rewrite H0. cbn. rewrite <- H2. apply H3. auto.
        * rewrite ?Compare_dec.leb_correct_conv; try lia.
        destruct (Hf  (n - N - 1)).
        exists (x0 + N + 1). 
        rewrite ?Compare_dec.leb_correct_conv; try lia.
        assert (x0 + N + 1 - N - 1 = x0) by lia. 
        rewrite H4.
        apply H.
Qed.

Theorem BDC_root_impl_BCC:
    BDC_root -> BCC.
Proof.
    intros DC A R _ H0.
    set (R' (p q:nat*A) := fst q = S (fst p) /\ R (fst p) (snd q)).
    destruct (H0 0) as (y0,Hy0).
    destruct (DC (prod nat A) ) with(R:=R') (a := (0, y0)) as (f,(Hf0,HfS)).
    - intros (n, a). destruct (H0 n) as [w Hw].
      exists (S n, w); easy.
    - assert (forall n, exists w, fst (f w) = n).
      + induction n.
      exists 0. now rewrite Hf0.
      destruct IHn as [w Hw].
      destruct (HfS w) as [y Hy].
      exists y. unfold R' in Hy.
      rewrite Hw in Hy.
      now destruct Hy.
      +  exists (fun n => snd (f n)).
      intro n'.
      destruct (H n') as [nw Hnw].
      specialize HfS with nw as [ny Hny].
      exists ny. 
      destruct Hny.
      now rewrite Hnw in H2.
Qed.

Theorem BDC_impl_BCC: BDC -> BCC.
Proof.
    intros ?; apply BDC_root_impl_BCC.
    now apply BDC_impl_BDC_root.
Qed.


End BDC_BCC.


Section incl.

    Definition incl_f {X} (f1 f2: nat -> X) := forall n, exists m, f1 n = f2 m.

End incl.

Notation "f1 ⊆ f2" := (incl_f f1 f2) (at level 30).

Section incl_fact.

    Definition trans_incl {X: Type} (f1 f2 f3: nat -> X) :
        f1 ⊆ f2 -> f2 ⊆ f3 -> f1 ⊆ f3.
    Proof.
        intros h1 h2 x.
        destruct (h1 x) as [y Hy].
        destruct (h2 y) as [z Hz].
        exists z; congruence.
    Qed.

End incl_fact.

Section merge.

    Definition even n := {m | n = 2 * m}.
    Definition odd n  := {m | n = 2 * m + 1}.
    Definition even_odd_dec n : even n + odd n.
    Proof.
        induction n as [|n [H1|H1]]; [left; exists 0; lia|..].
        - right; destruct H1 as [k H]; exists k; lia.
        - left; destruct H1 as [k H]; exists (S k); lia.
    Defined.

    Definition merge {X} (f1 f2: nat -> X): nat -> X :=
        fun n => match even_odd_dec n with 
            | inl L => f1 (proj1_sig L)
            | inr R => f2 (proj1_sig R)
        end.

End merge.

Notation "'to_merge_l' x" := (2 * x) (at level 30).
Notation "'to_merge_r' x" := (2 * x + 1) (at level 30).
Notation "f1 ∪ f2" := (merge f1 f2) (at level 34).

Section merge_fact.

    Context {X: Type}.
    Context (f1 f2 f3: nat -> X).

    Lemma union_eval_l x : (f1 ∪ f2) (to_merge_l x) = f1 x.
    Proof.
        unfold "∪"; destruct (even_odd_dec (to_merge_l x)).
        - destruct e; cbn; f_equal; nia.
        - destruct o. nia.
    Qed.

    Lemma union_eval_r x : (f1 ∪ f2) (to_merge_r x) = f2 x.
    Proof.
        unfold "∪"; destruct (even_odd_dec (to_merge_r x)).
        - destruct e. nia.
        - destruct o; cbn; f_equal; nia.
    Qed.

    Lemma union_incl_l : f1 ⊆ (f1 ∪ f2).
    Proof. now intros x; exists (to_merge_l x); rewrite union_eval_l. Qed.

    Lemma union_incl_r : f2 ⊆ (f1 ∪ f2).
    Proof. now intros x; exists (to_merge_r x); rewrite union_eval_r. Qed.

End merge_fact.


Section BCC_DDC_impl_BDC2.

    Section inner_mode.
(* Hypotheis we have *)
    Hypothesis BCC: BCC.
    Hypothesis DDC: DDC.

(* Promise by BDC2 *)
    Variable X: Type.
    Variable R: X -> X -> X -> Prop.
    Variable total_R: total_tr R.

(* Skolem relation *)
    Definition F (f1 f2: nat -> X) :=
        (forall n m, exists k, R (f1 n) (f1 m) (f2 k)) /\ (f1 ⊆ f2).

    Notation "f1 ⇒ f2" := (F f1 f2) (at level 29).

    Theorem trans_F: trans F.
    Proof.
        intros f1 f2 f3 [H1 H1'] [H2 H2']; split.
        - intros n m. destruct (H1 n m) as [w Hw].
          destruct (H2' w) as [ww Hww].
          exists ww; now rewrite <- Hww.
        - intros x; destruct (H1' x) as [y Hy]; destruct (H2' y) as [w Hw].
          exists w; congruence.
    Qed.

    Theorem total_F: total F.
    Proof using BCC total_R.
        intros f1.
        assert (forall n m, exists x, R (f1 n) (f1 m) x).
        firstorder.
        pose (R' n x := let '(n1, n2) := of_nat n in R (f1 n1) (f1 n2) x).
        destruct (@BCC X R') as [f2 Hf2]. exact (f1 42).
        { intros n; unfold R'; destruct (of_nat n); firstorder. }
        exists (f1 ∪ f2); split; [intros n m|].
        destruct (Hf2 (to_nat (n, m))) as [w Hw].
        exists (to_merge_r w); rewrite union_eval_r.  
        now unfold R' in Hw; rewrite cancel_of_to in Hw.
        apply union_incl_l.
    Qed.

    Theorem direct_F: direct F.
    Proof.
        intros f1 f2.
        destruct (total_F f1) as [f1' [Hf1 Hf1']], (total_F f2) as [f2' [Hf2 Hf2']].
        exists (f1' ∪ f2'); repeat split.
        - intros n m; destruct (Hf1 n m) as [k Hk].
          now exists (to_merge_l k); rewrite union_eval_l.
        - eapply trans_incl; [exact Hf1' | eapply union_incl_l].
        - intros n m; destruct (Hf2 n m) as [k Hk].
          now exists (to_merge_r k); rewrite union_eval_r.
        - eapply trans_incl; [exact Hf2' | eapply union_incl_r].
    Qed.

        Section inner_mode_by_direct_T.

        (* By DDC, there is a direct countable set *)
        Variable T: nat -> (nat -> X).
        Hypothesis direct_T: direct (F ∘ T).

        Definition f x := let '(n, m) := of_nat x in T n m.

        Fact eq_co_domain_f : f ⊆ f.
        Proof.
            now intros x; exists x.
        Qed.

        Lemma bounded_f:
            forall x y: nat, exists k a b, T k a = (f x) /\ T k b = (f y).
        Proof.
            intros x y; unfold f; 
            destruct (of_nat x) as [x1 x2], (of_nat y) as [y1 y2].
            destruct (direct_T x1 y1) as [w [[_ Hxw] [_ Hyw]]].
            destruct (Hxw x2) as [x3 Hx3], (Hyw y2) as [y3 Hy3].
            now exists w, x3, y3.
        Qed.

        Fact fixpoint_F: F f f.
        Proof.
            split; [intros n m| apply eq_co_domain_f].
            destruct (bounded_f n m) as [k (a & b & <- & <-)].
            destruct (direct_T k k) as [Sk [[Hk _] _]].
            destruct (Hk a b) as [w Hw].
            exists (to_nat (Sk, w)).
            now unfold f; rewrite cancel_of_to.
        Qed.

        End inner_mode_by_direct_T.

    Fact res: X -> exists f: nat -> X, (forall x y, exists z, R (f x) (f y) (f z)).
    Proof using DDC BCC total_R.
        intros x; edestruct (@DDC _  F (fun _ => x) trans_F   direct_F) as [T HT].
        exists (f T).
        now apply fixpoint_F.
    Qed.

    End inner_mode.

    Theorem res_BDC2: BCC -> DDC -> BDC2.
    Proof.
        intros BCC ddc X R x H.
        apply res; auto.
    Qed.

End BCC_DDC_impl_BDC2.


Section BDC2_impl_BCC_DDC.

    Lemma BDC2_impl_BDC: BDC2 -> BDC.
    Proof.
        intros H X R x Rtot.
        destruct (H X (fun x _ z => R x z) x) as [f Hf].
        { intros ? _; cbn. now eapply Rtot. }
        exists f. intros ?; eapply Hf.
        exact 42.
    Qed.

    Lemma BDC2_impl_DDC: BDC2 -> DDC.
    Proof.
        intros H X R x _ Rd.
        destruct (H X (fun x y z => R x z /\ R y z) x) as [f Hf].
        { intros a b; eapply Rd. }
        eexists f. intros a b.
        eapply Hf.
    Qed.



End BDC2_impl_BCC_DDC.


Section OBDC_implies_BDP_BEP_BDC2.

    Lemma OBDC_impl_BDP_on (A: Type): OBDC_on A -> BDP_on A.
    Proof.
        intros H P x.
        pose (R (x y z: A) := P x).
        destruct (H R x) as [f [_ Hf]].
        exists f; intros Hdp y.
        assert (forall x y, exists z, R (f x) (f y) (f z)) as H1.
        { intros ? ?; exists 42; unfold R; apply Hdp. }
        destruct (Hf H1 y y) as [? HP].
        now unfold R in HP.
    Qed.

    Lemma OBDC_impl_BEP_on (A: Type): OBDC_on A -> BEP_on A.
    Proof.
        intros H  P x.
        pose (R (x y z: A) := P z).
        destruct (H R x) as [f [Hf _]].
        exists f; intros Hdp.
        assert (forall x y, exists z, R x y z) as H1.
        { intros ? ?. unfold R. apply Hdp. }
        specialize (Hf H1 42 42). now unfold R in Hf.
    Qed.

    Lemma OBDC_impl_BDC2_on (X: Type): OBDC_on X -> BDC2_on X.
    Proof.
        intros H R x Htot.
        destruct (H R x) as [f Hf].
        rewrite Hf in Htot.
        exists f. apply Htot.
    Qed.
    

End OBDC_implies_BDP_BEP_BDC2.

Section DC_impl_DDC_BCC.

    Lemma DC_impl_DDC: DC -> DDC.
    Proof.
        intros DC A R a Tr H.
        destruct (DC A R a) as [f Hf].
        { intro x; destruct (H x x) as [z [Hz _]]; exists z; auto. }
        assert (forall x y, x < y -> R (f x) (f y)) as mono.
        { intros i j E.
          destruct (j - i) eqn:E'. lia.
          assert (j = i + S n) as -> by lia.
          induction n in i |-*. 
          rewrite Nat.add_1_r. apply Hf.
          eapply Tr. apply IHn. 
          rewrite !Nat.add_succ_r. apply Hf. }
          exists f; intros n m; exists (S (Nat.max n m)).
          split; apply mono; lia.
    Qed.

    Lemma DC_impl_BDC: DC -> BDC.
    Proof.
        intros H X R x Rtot.
        destruct (H X R x Rtot) as [f Hf].
        exists f. intros k. exists (S k).
        now apply Hf.
    Qed.

    Definition iter (n:nat) {A} (f:A->A) (x:A) : A :=
        nat_rect (fun _ => A) x (fun _ => f) n.

    Theorem BDC_AC00_impl_DC:
        BDC -> AC00 -> DC.
    Proof.
        intros BDC AC00 A R a tR. 
        destruct (BDC A R a tR) as [f Hf].
        destruct (AC00 (fun n m => R (f n) (f m)) 42 Hf) as [g Hg].
        exists (fun n => f (iter n (fun n => g n) 0)).
        intro n; cbn.
        now destruct (Hf ((iter n (fun n : nat => g n) 0))) as [[] Hg'].
    Qed.

    Lemma DC_impl_DC_root :
        DC -> DC_root.
    Proof.
        intros H X R HR x0.
        destruct (HR x0) as [y0 Hy0]. pose (a0 := exist _ y0 (@base _ R _ _ Hy0)).
        destruct (H { x | reachable R x0 x } (fun a b => R (proj1_sig a) (proj1_sig b)) a0) as [f Hf].
        -  intros [x Hx]. destruct (HR x) as [y Hy]. exists (exist _ y (@step _ R x0 y x Hx Hy)). apply Hy.
        - destruct (f 0) as [x Hx] eqn : H0.
            destruct (@reach_reach' _ _ _ _ Hx) as (g & N & H1 & H2 & H3).
            exists (fun n => if PeanoNat.Nat.leb n N then g n else proj1_sig (f (n - N - 1))). split.
            + cbn. apply H1.
            + intros n. assert (n <= N \/ n > N) as [Hn|Hn] by lia.
            * assert (S n <= N \/ n = N) as [Hn'| ->] by lia. 
                -- rewrite ?Compare_dec.leb_correct; try lia. now apply H3.
                -- rewrite Compare_dec.leb_correct, Compare_dec.leb_correct_conv; try lia.
                assert (S N - N - 1 = 0) as -> by lia. rewrite H0. cbn. rewrite <- H2. apply H3. auto.
            * rewrite ?Compare_dec.leb_correct_conv; try lia.
                assert (S n - N - 1 = S (n - N - 1)) as -> by lia. apply Hf.
    Qed.

    Lemma total_list {X Y} {R : X -> Y -> Prop} L :
        (forall x, exists y, R x y) -> exists L', Forall2 R L L'.
      Proof.
        intros HTot. induction L as [ | x L [L' IH]].
        - exists []. econstructor.
        - destruct (HTot x) as [y H]. exists (y :: L').
          now econstructor.
      Qed.

    Theorem DC_impl_CC: DC_root -> CC.
    Proof.
    intros dc A R a HR.
    destruct (HR 0) as [a0 HA].
    unshelve edestruct (dc (prod nat A) (fun p q => fst q = S (fst p) /\ R (fst p) (snd q))) as [f H].
    - exact (0, a0).
    - intros []. cbn. destruct (HR n) as [a' HA']. exists (S n, a'). cbn. tauto.
    - assert (HF : forall n, fst (f n) = n).
        { induction n. now rewrite (proj1 H). rewrite <- IHn at 2. apply H. }
        exists (fun n => snd (f (S n))). intros n. rewrite <- (HF n) at 1. apply H.
    Qed.

    Theorem CC_impl_BCC: CC -> BCC.
    Proof.
        intros H A R a Htot.
        destruct (H A R a Htot) as [f Hf].
        eexists f; intro n; exists n.
        eauto.
    Qed.


    Theorem CC_impl_AC00: CC -> AC00.
    Proof.
        intros H; apply H.
    Qed.

    Lemma CC_iff_BCC_AC00: CC <-> BCC /\ AC00.
    Proof.
        split.
        - intros CC; split; [apply CC_impl_BCC| apply CC_impl_AC00]; easy.
        - intros [bcc ac00] A R a totalR.
          destruct (bcc A R a totalR) as [f Pf].
          unfold AC00, CC_on in ac00.
          destruct (ac00 (fun x y => R x (f y))) as [g Pg]. exact 42.
          { intros x; apply Pf. }
         now exists (fun n => f (g n)).
    Qed.

End DC_impl_DDC_BCC.

Section LBDC_VBDC.

    Definition VBDC:=
        forall (A: Type) (R: forall {n}, vec A n -> A -> Prop), 
            A -> (forall n (v: vec A n), exists w, R v w) ->
            (exists f: nat -> A, forall n (v: vec nat n), exists m, R (Vector.map f v) (f m)).

    Definition LBDC :=
        forall (A: Type) (R: list A -> A -> Prop), 
            (forall (v: list A), exists w, R v w) ->
            (exists f: nat -> A, forall (v: list nat), exists m, R (map f v) (f m)).

    Fact any_length_sig n : Σ l: list nat, length l = n.
    Proof.
        exists ((fix f n := match n with | O => nil | S n => 0 :: (f n) end) n).
        induction n; try easy; cbn.
        now rewrite IHn.
    Qed.

    Fact LBDC_impl_BCC: LBDC -> BCC.
    Proof.
        intros BDC_list A R a total_R.
        pose (R' (l: list A) (a: A) := R (length l) (a)).
        destruct (BDC_list _ R') as [g Hg].
        - intro v; exact (total_R (length v)).
        - exists g. intro n.
          destruct (@any_length_sig n).
          destruct (Hg x) as [w Hw].
          exists w. unfold R' in Hw.
          now rewrite map_length, e in Hw.
    Qed.
    Fact to_map_of_eq_map {A B} (v: list A) (g: A -> B) : to_list (Vector.map g (of_list v)) = map g v.
    Proof.
        rewrite to_list_map.
        now rewrite to_list_of_list_opp.
    Qed.

    Fact length_map_to_list {A B n} (v: vec A n) (g: A -> B): length (map g (to_list v)) = n.
    Proof.
        rewrite map_length.
        now rewrite Vectors.vector_to_list_length.
    Qed.
    
    Lemma vec_list_map X Y n (v : Vector.t X n) (g : X -> Y) (H : n = length (map g (to_list v))) :
        of_list (map g (to_list v)) = cast (Vector.map g v) H.
    Proof.
        induction v; cbn; trivial. now rewrite <- IHv.
    Qed.
    
    Lemma cast_refl X n (v : Vector.t X n) :
        cast v (Logic.eq_refl) = v. 
    Proof.
        induction v; cbn; trivial. now rewrite IHv.
    Qed.
    
    Lemma vec_list_map' X Y n (P : forall n, Vector.t Y n -> Prop) (v : Vector.t X n) (g : X -> Y) :
        P (length (map g (to_list v))) (of_list (map g (to_list v))) <-> P n (Vector.map g v).
    Proof.
        assert (H : n = length (map g (to_list v))).
        - now rewrite map_length, length_to_list.
        - unshelve erewrite vec_list_map; try apply H.
        destruct H. now rewrite cast_refl.
    Qed.
    
    Lemma vec_list_map'' X Y n (P : forall n, Vector.t Y n -> Y -> Prop) (v : Vector.t X n) (g : X -> Y) w :
        P (length (map g (to_list v))) (of_list (map g (to_list v))) w <-> P n (Vector.map g v) w.
    Proof.
        assert (H : n = length (map g (to_list v))).
        - now rewrite map_length, length_to_list.
        - unshelve erewrite vec_list_map; try apply H.
        destruct H. now rewrite cast_refl.
    Qed.

    Fact LBDC_iff_VBDC: VBDC <-> LBDC .
    Proof.
    split.
    - intros BDC A R totalR.
        pose (R' n (l: vec A n) (a: A) := R (to_list l) a).
        destruct (totalR nil) as [a _].
        destruct (BDC _ R' a) as [g Hg].
        intros n v; exact (totalR (to_list v)).
        exists g; intro v. 
        destruct (Hg _ (of_list v)) as [w Hw]; exists w.
        unfold R' in Hw.
        now rewrite <- to_map_of_eq_map.
    - intros BDC_list A R a totalR.
        pose (R' (l: list A) (a: A) := R (length l) (of_list l) a).
        destruct (BDC_list _ R') as [g Hg].
        intro v; exact (totalR _ (of_list v)).
        exists g.  intros n v. 
        destruct (Hg (to_list v)) as [w Hw].
        unfold R' in Hw. exists w. revert Hw.
        now rewrite (vec_list_map'' R).
    Qed.

    Lemma LBDC_impl_BDC2: LBDC -> BDC2.
    Proof.
        intros ldc A R a HR.
        pose (R' := fun l y => match l with | a::b::_ => R a b y | _ => True end).
        destruct (ldc _ R') as [f Hf].
        - intros [|x [|y l]]; cbn; try now exists a.
          now destruct (HR x y) as [w Hw]; exists w.
        - exists f. intros n m. 
          destruct (Hf (n::m::nil) ) as [w Hw].
          now exists w.
    Qed.


End LBDC_VBDC.



Section Result.

    Theorem OBDC_impl_BDP_BEP_on (A: Type):
        OBDC_on A -> BDC2_on A /\ BDP_on A /\ BEP_on A.
    Proof.
        intros H; split;
        [now apply OBDC_impl_BDC2_on|now split; [apply OBDC_impl_BDP_on| apply OBDC_impl_BEP_on]].
    Qed.

    Theorem BDC2_iff_DDC_BCC:
        BDC2 <-> (DDC /\ BCC).
    Proof.
        split.
        - intros H; split. 
            now apply BDC2_impl_DDC.
            now apply BDC_impl_BCC, BDC2_impl_BDC.
        - intros [H1 H2]. now apply res_BDC2.
    Qed.

    Theorem DC_iff_BDC2_AC00: 
        DC <-> BDC /\ AC00.
    Proof.
        split; intros H.
        - split; [now apply DC_impl_BDC |now apply CC_impl_AC00, DC_impl_CC, DC_impl_DC_root].
        - now destruct H; apply BDC_AC00_impl_DC; [|easy].
    Qed.

    Theorem DC_iff_DDC_AC00:
        DC <-> BDC2 /\ AC00.
    Proof.
        split.
        - intros H; split.
          rewrite BDC2_iff_DDC_BCC; split.
          now apply DC_impl_DDC.
          now apply CC_impl_BCC, DC_impl_CC, DC_impl_DC_root.
          now apply CC_impl_AC00, DC_impl_CC, DC_impl_DC_root.
        - intros [H1 H2]. rewrite DC_iff_BDC2_AC00; split; [|easy].
          now apply BDC2_impl_BDC.
    Qed.

    Fact CC_impl_BCC_on (A: Type): CC_on A -> BCC_on A.
    Proof.
        intros H R a Htot.
        destruct (H R a Htot) as [f Hf].
        eexists f; intro n; exists n.
        eauto.
    Qed.

    Fact DC_impl_BDC_on (A: Type): DC_on A -> BDC_on A.
    Proof.
        intros H R a Htot.
        destruct (H R a Htot) as [f Hf].
        exists f; intros x; exists (S x).
        unfold consf; eauto.
    Qed.

    Fact BDC2_impl_BDC_on (A: Type): BDC2_on A -> BDC_on A. 
    Proof.
        intros H R a Htot.
        destruct (H (fun x _ z => R x z) a) as [f Hf].
        { intros x _; eauto. }
        exists f. intros x. 
        destruct (Hf x 42) as [w Hw]; eauto.
    Qed.

End Result.


Section BDP_BEP_scheme.

    Definition BDP_scheme (domain range: Type) :=
        forall P: domain -> Prop, domain -> exists f: range -> domain,
            (forall n: range, P (f n)) -> forall x, P x.

    Definition BEP_scheme (domain range: Type) :=
        forall P: domain -> Prop, domain -> exists f: range -> domain,
            (exists x, P x) -> (exists m, P (f m)).

End BDP_BEP_scheme.

Notation BDP_to A := (forall domain, @BDP_scheme domain A).
Notation BEP_to A := (forall domain, @BEP_scheme domain A).

Notation BDP' := (@BDP_to nat).
Notation BEP' := (@BEP_to nat).

Notation DP := (@BDP_to unit).
Notation EP := (@BEP_to unit).

Notation BDP₁ := (@BDP_scheme nat unit).
Notation BEP₁ := (@BEP_scheme nat unit).


Section scheme_facts.

    Definition WPFP := (forall b: nat -> bool, exists a: nat -> bool, (exists n, b n = false) <-> (forall n, a n = true)).
    Definition LEM := (forall P, P \/ ~ P).
    Definition LPO := (forall f : nat -> bool, (forall x, f x = false) \/ (exists x, f x = true)).
    Definition IP := forall (A:Type) (P:A -> Prop) (Q:Prop), inhabited A -> (Q -> exists x, P x) -> exists x, Q -> P x.
    Definition BIP := forall (A:Type) (P:A -> Prop) (Q:Prop), inhabited A -> (Q -> exists x, P x) -> exists (f: nat -> A), Q -> (exists m, P (f m)).
    Definition KS := forall P, exists f : nat -> bool, P <-> exists n, f n = true.
    Definition KS' := forall P, exists f : nat -> bool, ~ P <-> forall n, f n = true.
    Definition ODC := forall X (R: X -> X -> Prop) , X -> exists f: nat -> X, total R -> forall n, R (f n) (f (S n)).

    Lemma BDP_impl_KS':
        BDP -> KS'.
    Proof.
        intros dp P.
        destruct (dp (option P) 
            (fun x => match x with Some x => ~ P | _ => True end)) as [f H].
        exact None.
        exists (fun n => if f n then false else true). split.
        - intros HP. intros n. destruct (f n); tauto.
        - intros H'. intros HP.  refine (H _ (Some HP) _); try tauto.
            intros n. specialize (H' n). destruct (f n); try tauto. discriminate.
    Qed.

    Fact DP_is_DP: 
        DP <-> (forall A (P: A -> Prop), A -> exists x, P x -> forall x, P x).
    Proof.
        split; intros.
        - destruct (H A P); try easy.
            exists (x tt); intro h.
            apply H0. now intros [].
        - intros P a. destruct (H domain P); try easy.
            exists (fun _ => x).
            intros; now apply H0, H1.
    Qed.

    Fact EP_is_EP: 
        EP <-> (forall A (P : A -> Prop), A -> exists x, (exists x, P x) -> P x).
    Proof.
        split; intros.
        - destruct (H A P); try easy.
            exists (x tt); intro h.
            destruct H0 as [[] Pu]; easy. 
        - intros P a. destruct (H domain P); try easy.
            exists (fun _ => x).
            intros. exists tt. now apply H0, H1.
    Qed.

    Lemma DP_impl_LEM : DP -> LEM.
    Proof.
        intros dp P.
        rewrite DP_is_DP in dp.
        destruct (dp (option (P \/ ~ P)) (fun x => match x with Some x => ~ P | _ => True end) None) as [[x|] H].
        - exact x.
        - right. intros HP. now apply (H I (Some (or_introl HP))).
    Qed.

    Lemma DP_iff_LEM : DP <-> LEM.
    Proof.
        split. apply DP_impl_LEM.
        intros H X P x.
        destruct (H (exists x, ~ P x)) as [L|R].
        - destruct L as [w Pw].
          exists (fun _ => w). intros Px. 
          specialize (Px tt). exfalso. easy.
        - exists (fun _ => x). intros _ w.
          destruct (H (P w)); [easy|].
          exfalso. apply R. now exists w.
    Qed. 

    Lemma EP_impl_LEM : EP -> LEM.
    Proof.
        intros dp P.
        rewrite EP_is_EP in dp.
        destruct 
        (dp (option (P \/ ~ P))  (fun x => match x with  |Some x => P  | _ => False end)  None) as [[x|] H].
        - exact x.
        - right. intros HP. apply H. exists (Some (or_introl HP)). exact HP.
    Qed.

    Lemma EP_iff_LEM: EP <-> LEM.
    Proof.
        split. apply EP_impl_LEM.
        intros H X P x.
        destruct (H (exists x, P x)) as [[w Pw]|R].
        - exists (fun _ => w). intros _. now exists tt. 
        - exists (fun _ => x). intros [w Pw].
          exfalso. apply R. now exists w.
    Qed.

    Lemma KS_LPO_LEM: KS -> LPO -> LEM.
    Proof.
        intros KS LPO P. 
        destruct (KS P) as [f Pf].
        destruct (LPO f) as [H|H].
        - right; intro p. 
            rewrite Pf in p.
            destruct p as [w Pw].
            specialize (H w).
            congruence.
        - left; now rewrite Pf.
    Qed.

    Lemma BDP_LPO_impl_LEM : BDP -> LPO -> LEM.
    Proof.
        intros dp lpo P.
        destruct (dp (option (P \/ ~ P)) (fun x => match x with Some x => ~ P | _ => True end) None) as [f H].
        destruct (lpo (fun n => if f n then true else false)) as [Hf|[x Hx]].
        - right. intros HP. refine (H _ (Some (or_introl HP)) HP).
            intros n. specialize (Hf n). destruct (f n); try discriminate. trivial.
        - destruct (f x); try discriminate. trivial.
    Qed.

    Lemma BDP₁_impl_LPO: BDP₁ -> LPO.
    Proof.
        intros dp f. 
        specialize (dp (fun n => f n = false)).
        destruct dp; [exact 42|].
        destruct (f (x tt)) eqn: E.
        - right. now exists (x tt).
        - left.  apply H. now intros [].
    Qed.

    Fact EP_impl_IP: EP -> IP.
    Proof.
        intros.
        intros A P Q [] HP.
        destruct (H A P X). 
        exists (x tt); intros Q'%HP.
        destruct H0 as [[] P']; easy.
    Qed.

    Fact IP_impl_EP: IP -> EP.
    Proof.
        intros IP A P.
        intros IA.
        destruct (IP A P (exists x, P x)).
        now constructor.
        easy.
        exists (fun v => x).
        intros P'. exists tt. now apply H.
    Qed.

    Fact BEP_impl_BIP: BEP -> BIP.
    Proof.
        intros BDP' A P Q [] HP.
        destruct (BDP' A P X).
        exists x; intros Q'%HP.
        now apply H.
    Qed.
    
    Fact BIP_impl_BEP: BIP -> BEP.
    Proof.
        intros BIP A P a.
        destruct (BIP A P (exists x, P x)). { now constructor. }
        easy.
        now exists x.
    Qed.

    Fact DC_IP_implies_ODC: DC -> IP -> ODC.
    Proof.
        intros DC IP A R w.
        specialize (DC_impl_DC_root DC) as DC_r.
        apply IP. constructor; exact (fun _ => w).
        intros DC'%(DC A R); eauto.
    Qed.

End scheme_facts.

