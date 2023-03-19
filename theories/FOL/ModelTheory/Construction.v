Require Import Undecidability.FOL.ModelTheory.Core.
Require Import Coq.Arith.Compare_dec.
Require Import Undecidability.FOL.ModelTheory.SearchNat.
Require Import Undecidability.FOL.ModelTheory.HenkinModel.


Notation "'Σ' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Section incl_def.

    Variables A B C: Type.

    Definition im_incl (ρ: A -> C) (ρ': B -> C) := forall x, Σ y, ρ x = ρ' y.
    Definition im_incl_k (ρ: nat -> C) (ρ': B -> C)  k := forall x, x < k -> Σ y, ρ x = ρ' y.
    Definition im_sub (ρ: A -> C) (ρ': B -> C)  := forall x, exists y, ρ x = ρ' y.

End incl_def.

    Notation "ρ ≼ ρ'" := (im_incl ρ ρ') (at level 25).
    Notation "ρ ≼[ k ] ρ'" := (im_incl_k ρ ρ' k) (at level 25).
    Notation "ρ ⊆ ρ'" := (im_sub ρ ρ') (at level 25).

Section Construction.

    Context {Σf : funcs_signature} {Σp : preds_signature} {M: model}. 

    Section incl_prop.

    Lemma sat_incl ρ ρ': ρ ≼ ρ' -> forall φ, 
        exists σ, (M ⊨[ρ] φ <-> M ⊨[ρ'] φ[σ]) /\ (forall x, (σ >> (eval M interp' ρ')) x = ρ x).
    Proof.
        intros H φ.
        exists (fun x => $ (projT1 (H x))).
        rewrite sat_comp; split.
        apply sat_ext.
        all: intro x; cbn; now destruct (H x).
    Qed.

    Lemma bounded_incl ρ ρ' φ k: bounded k φ -> ρ ≼[k] ρ' -> 
        exists σ, (M ⊨[ρ] φ <-> M ⊨[ρ'] φ[σ]) /\ 
            (forall x, x < k -> (σ >> (eval M interp' ρ')) x = ρ x).
    Proof.
        intros.
        exists (fun x => match (lt_dec x k) with
                | left cp =>  $ (projT1 (X x cp)) 
                | right _ =>  $ x 
                end).
        rewrite sat_comp.
        split.
        apply bound_ext with k. exact H.
        intros; cbn.
        destruct (lt_dec n k); cbn.
        now destruct (X n l).
        congruence.
        intros x l; cbn.
        destruct (lt_dec x k); cbn.
        now destruct (X x l0).
        congruence.
    Qed.

    Lemma map_cons_w (ρ ρ': env M) w  {n} (v: vec term n): 
        (forall t : term, In t v -> t ₜ[ M] ρ' = t`[fun x : nat => $(S x)] ₜ[ M] (w .: ρ') )
            -> map (eval M interp' ρ') v = map (eval M interp' (w .: ρ')) (map (subst_term (fun x : nat => $(S x))) v).
    Proof.
        intro H.
        induction v; cbn. {constructor. }
        rewrite IHv, (H h). {easy. }
        constructor.
        intros t H'; apply H.
        now constructor.
    Qed.

    Lemma cons_w (ρ ρ': env M) (σ: nat -> term) w:
        forall x, (σ >> eval M interp' ρ') x = (σ >> subst_term ↑) x ₜ[ M] (w .: ρ').
    Proof.
        unfold ">>".
        intro x; induction (σ x); cbn; try easy.
        now rewrite map_cons_w with (w := w).
    Qed.

    Definition wit_env (ρ ρ_s: env M) φ := exists w, M ⊨[ρ_s w .: ρ] φ -> M ⊨[ρ] (∀ φ).

    Definition wit_env_ω (ρ ρ_s: env M) φ := (forall n: nat, M ⊨[ρ_s n .: ρ] φ) -> M ⊨[ρ] (∀ φ).

    Lemma incl_impl_wit_env ρ ρ' ρ_s: ρ ≼ ρ' 
        -> (forall φ, wit_env ρ' ρ_s φ) -> (forall φ, wit_env ρ ρ_s φ).
    Proof.
        intros.
        destruct (sat_incl X (∀ φ)) as (σ & fH & EH).
        destruct (H (φ[up σ])) as [ws P].
        exists ws.
        intro Hp; rewrite fH. 
        apply P; revert Hp.
        rewrite sat_comp.
        apply sat_ext'.
        destruct x; cbn. { easy. }
        rewrite <- EH.
        apply (cons_w ρ ρ' σ (ρ_s ws)).
    Qed.

    Lemma bounded_incl_impl_wit_env ρ ρ' ρ_s: (forall φ, wit_env ρ' ρ_s φ) 
        -> (forall φ k, bounded k φ -> ρ ≼[k] ρ' -> wit_env ρ ρ_s φ).
    Proof.
        intros Rρ' φ k H Ink.
        assert (bounded k (∀ φ)) as HS.
        apply bounded_S_quant.
        apply (bounded_up H); lia.
        destruct (bounded_incl HS Ink ) as (σ & fH & EH).
        destruct (Rρ' (φ[up σ])) as [ws P].
        exists ws.
        intro Hp; rewrite fH. 
        apply P; revert Hp.
        rewrite sat_comp.
        apply (bound_ext _ H); intros n Ln. 
        destruct n; cbn. {easy. }
        rewrite <- EH.
        - now rewrite (cons_w ρ ρ' σ (ρ_s ws)).
        - lia.
    Qed.  

    Lemma bounded_incl_impl_wit_env_ω ρ ρ' ρ_s: (forall φ, wit_env_ω ρ' ρ_s φ) 
    -> (forall φ k, bounded k φ -> ρ ≼[k] ρ' -> wit_env_ω ρ ρ_s φ).
    Proof.
        intros Rρ' φ k H Ink.
        assert (bounded k (∀ φ)) as HS.
        apply bounded_S_quant.
        apply (bounded_up H); lia.
        destruct (bounded_incl HS Ink ) as (σ & fH & EH).
        specialize (Rρ' (φ[up σ])) as P.
        intro Hp; rewrite fH. 
        apply P; revert Hp.
        intros H' n'.
        rewrite sat_comp.
        unshelve eapply (bound_ext _ H). exact (ρ_s n' .: ρ). 
        intros n Ln. 
        destruct n; cbn. {easy. }
        rewrite <- EH.
        - now rewrite (cons_w ρ ρ' σ (ρ_s n')).
        - lia.
        - apply H'.
    Qed.  

    End incl_prop.

    Section incl_Path.

    Variable F: nat -> nat -> M.

    Hypothesis prop_F: forall n, (F n) ≼ (F (S n)).

    Lemma refl_incl (e: env M): e ≼ e.
    Proof.
        intros x.
        now exists x.
    Qed.

    Lemma trans_incl (a b c: env M): a ≼ b -> b ≼ c -> a ≼ c.
    Proof.
        unfold "≼"; intros.
        destruct (H x) as [ny H'], (H0 ny) as [my H''].
        exists my; congruence.
    Qed.

    Lemma nil_F:
        forall n, F 0 ≼ F n.
    Proof.
        induction n. 
        - apply refl_incl.
        - eapply trans_incl.
          apply IHn.
          easy.
    Qed.

    Lemma mono_F' a b: F a ≼ F (a + b) .
    Proof.
        induction b.
        - assert (a + 0 = a) as -> by lia; apply refl_incl.
        - assert (a + S b = S(a + b)) as -> by lia.
          eapply trans_incl. exact IHb. exact (prop_F (a + b)).
    Qed.

    Lemma mono_F a b: a < b -> F a ≼ F b.
    Proof.
        assert (a < b -> Σ c, a + c = b) .
        intro H; exists (b - a); lia.
        intro aLb.
        destruct (H aLb) as [c Pc].
        specialize (mono_F' a c).
        now rewrite Pc. 
    Qed.

    End incl_Path.

    Section Fixed_point.

    Variable F: nat -> nat -> M.

    Definition wit_rel ρ ρ' :=
        (forall φ, wit_env ρ ρ' φ) /\  ρ ⊆ ρ'.

    Definition wit_rel_comp ρ ρ' :=
        (forall φ, wit_env ρ ρ' φ) /\ forall x, ρ x = ρ' (2 * x).

    Variable init_ρ: nat -> M.

    Hypothesis depandent_path:
        F 0 = init_ρ /\ forall n, wit_rel_comp (F n) (F (S n)).

    Lemma wit_rel_comp_implies_incl ρ ρ':
        wit_rel_comp ρ ρ' -> ρ ≼ ρ'.
    Proof.
        intros H x; exists (2 * x).
        now destruct H as [_ P].
    Qed.

    Lemma depandent_path_comp:
        forall n, F n ≼ F (S n) .
    Proof.
        destruct depandent_path as [_ H].
        now intro n; eapply wit_rel_comp_implies_incl.
    Qed.

    Opaque encode_p. 

    Definition fixed x := F (π__1 x) (π__2 x).

    Lemma union_incl n: (F n) ≼ fixed.
    Proof.
        intro x; exists (encode n x); cbn.
        unfold fixed.
        now rewrite cantor_left, cantor_right.
    Qed.

    Lemma union_fixed n: wit_rel (F n) fixed.
    Proof.
        split; intros.
        - unfold wit_env. 
          destruct depandent_path as [_ H].
          destruct (H n) as [H_ H_'].
          destruct (H_ φ) as [w H'].
          (* destruct (H'' w) as [w' Pw]. *)
          destruct (union_incl (S n) w) as [ws Pws].
          exists ws.
          intro; apply H'.
          now rewrite Pws.
        - intro x; exists (encode n x); cbn.
          unfold fixed.
          now rewrite cantor_left, cantor_right.
    Qed.

    Lemma bounded_cantor b:
        Σ E, forall x, x < b -> π__1 x < E.
    Proof.
        clear; strong induction b.
        specialize (H (pred b)).
        destruct b; [exists 0; intros; lia| ].
        destruct H as [Ep EP]; [lia |].
        destruct (lt_dec Ep ((π__1 b))); 
        exists (S (π__1 b)) + exists (S Ep); 
        intros x H'; destruct (lt_dec x b); specialize (EP x); 
        lia || now assert (x = b) as -> by lia; lia.
    Qed.


    Lemma bounded_rel b: 
        Σ E: nat, fixed ≼[b] (F E).
    Proof.
        destruct (bounded_cantor b) as [E PE].
        exists E; intros x H.
        unfold fixed.
        specialize (PE _ H).
        specialize (mono_F depandent_path_comp PE) as H1.
        exists (projT1 (H1 (π__2 x))).
        now destruct (projT2 (H1 (π__2 x))).
    Qed.


    Theorem Fixed_point:
        wit_rel fixed fixed .
    Proof.
        split; intros.
        - destruct (find_bounded φ) as [b bφ].
          destruct (bounded_rel b) as [E P].
          (* enough (exists E: nat, forall x, x < b -> exists y, fixed x = F E y) as [E P]. *)
          unshelve eapply bounded_incl_impl_wit_env; [exact (F E) |exact b | |easy |..].
          + now destruct (union_fixed E) as [HB _].
          + intros x Lxb; apply (P x Lxb). 
        - intro x; now exists x.
    Qed.

    End Fixed_point.

    Section Fixed_point_ω.

    Variable F: nat -> nat -> M.

    Definition wit_rel_ω ρ ρ' :=
        (forall φ, wit_env_ω ρ ρ' φ) /\ ρ ⊆ ρ'.

    Definition wit_rel_comp_ω ρ ρ' :=
        (forall φ, wit_env_ω ρ ρ' φ) /\ forall x, ρ x = ρ' (2 * x).

    Variable init_ρ: nat -> M.

    Hypothesis depandent_path_ω:
        F 0 = init_ρ /\ forall n, wit_rel_comp_ω (F n) (F (S n)).

    Lemma wit_rel_comp_implies_incl_ω ρ ρ':
        wit_rel_comp_ω ρ ρ' -> ρ ≼ ρ'.
    Proof.
        intros H x; exists (2 * x).
        now destruct H as [_ P].
    Qed.

    Lemma depandent_path_comp_ω:
        forall n, F n ≼ F (S n) .
    Proof.
        destruct depandent_path_ω as [_ H].
        now intro n; eapply wit_rel_comp_implies_incl_ω.
    Qed.

    Opaque encode_p. 

    Definition fixed_ω x := F (π__1 x) (π__2 x).

    Lemma union_incl_ω n: (F n) ≼ fixed_ω.
    Proof.
        intro x; exists (encode n x); cbn.
        unfold fixed_ω.
        now rewrite cantor_left, cantor_right.
    Qed.

    Lemma union_fixed_ω n: wit_rel_ω (F n) fixed_ω.
    Proof.
        split; intros.
        - unfold wit_env. 
          destruct depandent_path_ω as [_ H].
          destruct (H n) as [H_ H_'].
          specialize (H_ φ) as H'. 
          (* destruct (H'' w) as [w' Pw]. *)
          specialize (union_incl_ω (S n)) as  Pws.
          unfold wit_env_ω.
          intros Ha n'. apply H'.
          unfold "≼" in Pws.
          intro w.
          destruct (Pws w) as [w' ->].
          now specialize (Ha w').
        - intro x; exists (encode n x); cbn.
          unfold fixed_ω.
          now rewrite cantor_left, cantor_right.
    Qed.

    Lemma bounded_rel_ω b: 
        Σ E: nat, fixed_ω ≼[b] (F E).
    Proof.
        destruct (bounded_cantor b) as [E PE].
        exists E; intros x H.
        unfold fixed.
        specialize (PE _ H).
        specialize (mono_F depandent_path_comp_ω PE) as H1.
        exists (projT1 (H1 (π__2 x))).
        now destruct (projT2 (H1 (π__2 x))).
    Qed.

    Theorem Fixed_point_ω:
        wit_rel_ω fixed_ω fixed_ω.
    Proof.
        split; intros.
        - destruct (find_bounded φ) as [b bφ].
          destruct (bounded_rel_ω b) as [E P].
          (* enough (exists E: nat, forall x, x < b -> exists y, fixed x = F E y) as [E P]. *)
          unshelve eapply bounded_incl_impl_wit_env_ω; [exact (F E) |exact b | |easy |..].
          + now destruct (union_fixed_ω E) as [HB _].
          + intros x Lxb; apply (P x Lxb). 
        - intro x; now exists x.
    Qed.

    End Fixed_point_ω.

    Section wit_rel_by_DC.

    Definition Even n := Σ m, n = 2 * m.
    Definition Odd n := Σ m, n = 2 * m + 1.
    Definition Even_Odd_dec n : Even n + Odd n.
    Proof.
        induction n as [|n [H1|H1]]; [left; exists 0; lia|..].
        - right; destruct H1 as [k H]; exists k; lia.
        - left; destruct H1 as [k H]; exists (S k); lia.
    Defined.

    Lemma not_Even_Odd_both n: 
         (Even n) * (Odd n) -> False.
    Proof.
        intros ([k Pk] &[t Pt]); lia.
    Qed.

    (* If the signature is countable *)
    Variable phi_ : nat -> form.
    Variable nth_ : form -> nat.
    Hypothesis Hphi : forall phi,  phi_ (nth_ phi) = phi.

    Hypothesis DC: DC.

    Theorem AC_ω: AC_ω.
     Proof.
       intros A R H0.
       set (R' (p q:nat*A) := fst q = S (fst p) /\ R (fst p) (snd q)).
       destruct (H0 0) as (y0,Hy0).
       destruct (@DC (nat*A)) with(R:=R') (w:=(0,y0)) as (f,(Hf0,HfS)).
       - intro x; destruct (H0 (fst x)) as (y,Hy).
         exists (S (fst x),y).
         red. auto.
       - assert (Heq:forall n, fst (f n) = n).
         + induction n.
           * rewrite Hf0; reflexivity.
           * specialize HfS with n; destruct HfS as (->,_); congruence.
         + exists (fun n => snd (f (S n))).
           intro n'. specialize HfS with n'.
           destruct HfS as (_,HR).
           rewrite Heq in HR.
           assumption.
     Qed.

    Definition AC_form: AC_form.
    Proof.
        intros A R total_R.
        set (R' n := R (phi_ n)).
        assert (total_rel R') as total_R'. intro x. 
        now destruct (total_R (phi_ x)) as [b Pb]; exists b.
        destruct (AC_ω total_R') as [f Pf].
        exists (fun fm => f (nth_ fm)).
        intro x; specialize (Pf (nth_ x)).
        unfold R' in Pf.
        now rewrite (Hphi x) in Pf.
    Qed.

    Hypothesis DP: DP.
    Hypothesis DP_ω: DP_ω.

    Lemma iterater_snd P: (forall n, P (π__2 n)) -> (forall n, P n).
    Proof.
        intros.
        specialize (X (encode 0 n)).
        now rewrite cantor_right in X.
    Qed.
    
    Definition AC_app_ω: 
        forall ρ, exists (W: nat -> M), forall φ, (forall w, M ⊨[W w.:ρ] φ) -> M ⊨[ρ] ∀ φ.
    Proof.
        intros.
        destruct (@AC_form (nat -> M) (fun phi h => (forall w, M ⊨[(h w) .: ρ] phi) -> M ⊨[ρ] (∀ phi))) as [F PF].
        - intro φ; destruct (DP_ω (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
          constructor; exact (ρ O). exists w; intro Hx; cbn; now apply Hw.
        - exists (fun n: nat => F (phi_ (π__1 n)) (π__2 n)).
          intro φ; specialize (PF φ).
          intro H'. apply PF.
          intro w.
          specialize (H' (encode (nth_ φ) w)).
          rewrite cantor_left, cantor_right in H'.
          now rewrite (Hphi φ) in H'.
    Qed.

    Definition AC_app: 
        forall ρ, exists (W: nat -> M), forall φ, exists w, M ⊨[W w.:ρ] φ -> M ⊨[ρ] ∀ φ.
    Proof.
        intros.
        destruct (@AC_form M (fun phi w => M ⊨[w .: ρ] phi -> M ⊨[ρ] (∀ phi))) as [F PF].
        - intro φ; destruct (DP (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
          constructor; exact (ρ O). exists w; intro Hx; cbn; now apply Hw.
        - exists (fun n: nat => F (phi_ n)).
          intro φ; specialize (PF φ).
          now exists (nth_ φ); rewrite (Hphi φ).
    Qed.

    Definition path root:
        exists F, F O = root /\ forall n, wit_rel_comp (F n) (F (S n)).
    Proof.
        unshelve eapply (DC  _ root).
        intro ρ; destruct (AC_app ρ) as [W P].
        unfold wit_rel_comp.
        exists (fun n => match Even_Odd_dec n with 
                | inl L => ρ (projT1 L)
                | inr R => W (projT1 R)
                end ); split.
        - intros phi; destruct (P phi) as [w Pw].
          exists (2 * w + 1).
          assert (Odd (2 * w + 1)) by (exists w; lia).
          destruct (Even_Odd_dec (2 * w + 1)) eqn: E.
          now exfalso; apply (@not_Even_Odd_both (2*w + 1)).
          intro; apply Pw.
          specialize (projT2 o) as H'; cbn in H'.
          enough (pi1 o = w) as <- by easy.
          now enough ( (w + (w + 0)) + 1 = (pi1 o + (pi1 o + 0)) + 1) by lia.
        - intro x. destruct (Even_Odd_dec (2 * x)) eqn: E.
          destruct e; cbn; enough (x = x0) as -> by easy; nia.
          exfalso; eapply (@not_Even_Odd_both (2*x)); split; [now exists x| easy].  
    Qed.

    Definition path_ω root:
        exists F, F O = root /\ forall n, wit_rel_comp_ω (F n) (F (S n)).
    Proof.
        unshelve eapply (DC  _ root).
        intro ρ; destruct (AC_app_ω ρ) as [W P].
        exists (fun n => match Even_Odd_dec n with 
                | inl L => ρ (projT1 L)
                | inr R => W (projT1 R)
                end ); split.
        - intros phi; specialize (P phi) as Pw.
          intros H' w'.
          apply Pw; intro w.
          assert (Odd (2 * w + 1)) by (exists w; lia).
          destruct (Even_Odd_dec (2 * w + 1)) eqn: E.
          now exfalso; apply (@not_Even_Odd_both (2*w + 1)).
          specialize (H' (2*w + 1)).
          rewrite E in H'.
          specialize (projT2 o) as H_; cbn in H_.
          enough (pi1 o = w) as <- by easy.
          now enough ( (w + (w + 0)) + 1 = (pi1 o + (pi1 o + 0)) + 1) by lia.
        - intro x. destruct (Even_Odd_dec (2 * x)) eqn: E.
          destruct e; cbn; enough (x = x0) as -> by easy; nia.
          exfalso; eapply (@not_Even_Odd_both (2*x)); split; [now exists x| easy].  
    Qed.

    End wit_rel_by_DC.

End Construction.

Section Result.

    (* For any countable signature Σ *)
    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Variable phi_: nat -> form.
    Variable nth_: form -> nat.
    Hypothesis Hphi: forall phi,  phi_ (nth_ phi) = phi.

    (* For any model over Σ, there is an elementary submodel *)
    Theorem LS_downward: 
        DP -> DC -> forall (M: model) (root: env M), exists (N: model), N ⪳ M.
    Proof.
        intros DP DC M root.
        destruct (path Hphi DC DP) with (root := root) as [F PF].
        pose (depandent_path_comp PF) as Incl;
        pose (Fixed_point PF) as Fixed_point.
        apply Tarski_Vaught_Test' with (phi_ := phi_) (h := fixed F).
        { now intro phi; exists (nth_ phi); rewrite Hphi. }
        now destruct Fixed_point.
    Qed.

    (* This version show that the elementary submodel include all elements in root *)
    Theorem LS_downward': 
        DP -> DC -> forall (M: model) (root: env M), 
            exists (N: model) (mor: N -> M), N ⪳[mor] M /\ root ⊆ mor.
    Proof.
        intros DP DC M root.
        destruct (path Hphi DC DP) with (root := root) as [F PF].
        pose (depandent_path_comp PF) as Incl;
        pose (Fixed_point PF) as Fixed_point.
        apply Tarski_Vaught_Test_with_root with (phi_ := phi_) (h := fixed F) (root := root).
        { now intro phi; exists (nth_ phi); rewrite Hphi. }
        intro x; destruct (union_incl F 0 x) as [y Py].
        exists y; rewrite <- Py; destruct PF as [A B]; now rewrite A.
        now destruct Fixed_point.
    Qed.

    Theorem LS_downward_from_DPω_and_DC: 
        DP_ω -> DC -> forall (M: model) (root: env M), exists (N: model), N ⪳ M.
    Proof.
        intros DP_ω DC M root.
        destruct (path_ω Hphi DC DP_ω ) with (root := root) as [F PF].
        pose (depandent_path_comp_ω PF) as Incl;
        pose (Fixed_point_ω PF) as Fixed_point.
        apply Tarski_Vaught_Test_ω' with (phi_ := phi_) (h := fixed F).
        { now intro phi; exists (nth_ phi); rewrite Hphi. }
        now destruct Fixed_point.
    Qed.

End Result.





