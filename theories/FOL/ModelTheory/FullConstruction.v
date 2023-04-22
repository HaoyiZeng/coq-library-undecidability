Require Import Undecidability.FOL.Completeness.TarskiCompleteness.
Require Import Lia Peano_dec.
Require Import Undecidability.FOL.ModelTheory.FullModelNotation.
Require Import Undecidability.FOL.ModelTheory.SearchNat.
Require Import Undecidability.FOL.ModelTheory.FullHenkinModel.
Require Import Undecidability.FOL.ModelTheory.DCFull.

Local Set Implicit Arguments.

Section Incl_im.
    Variables A B C: Type.

    Definition im_sub (ρ: A -> C) (ρ': B -> C)  := forall x, exists y, ρ x = ρ' y.
    Definition im_sub_k (ρ: nat -> C) (ρ': B -> C)  k := forall x, x < k -> exists y, ρ x = ρ' y.

End Incl_im.

Notation "ρ ⊆ ρ'" := (im_sub ρ ρ') (at level 25).
Notation "ρ ⊆[ k ] ρ'" := (im_sub_k ρ ρ' k) (at level 25).

Section Incl_facts.

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

    Lemma refl_sub {A B} (e: A -> B): e ⊆ e.
    Proof.
        intros x.
        now exists x.
    Qed.

    Lemma trans_sub  {A B} (a b c: A -> B): a ⊆ b -> b ⊆ c -> a ⊆ c.
    Proof.
        unfold "⊆"; intros.
        destruct (H x) as [ny H'], (H0 ny) as [my H''].
        exists my; congruence.
    Qed.

End Incl_facts.


Section AnyModel.
    Context {Σf : funcs_signature} {Σp : preds_signature} {M: model}. 

Section Henkin_condition.
    Definition succ (ρ: env M) (ρ_s: env M) (φ: form): Prop :=
        ((forall n: nat, M ⊨[ρ_s n .: ρ] φ) -> M ⊨[ρ] (∀ φ)) 
            /\ 
        (M ⊨[ρ] (∃ φ) -> exists m, M ⊨[ρ_s m .: ρ] φ).
End Henkin_condition.

Notation "ρ ⇒ ρ_s" := (forall φ, succ ρ ρ_s φ) (at level 25).
Notation "ρ ⇒[ phi ] ρ_s" := (succ ρ ρ_s phi) (at level 25).

Section Technical_lemma.

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
    
    Lemma im_bounded_sub (ρ ρ': env M) b:
        ρ ⊆[b] ρ' -> exists (ξ : nat -> nat), forall x, x < b -> (ρ x) = (ρ' (ξ x)).
    Proof.
        induction b; cbn; [intros |].
        - exists (fun _ => O); lia.
        - intros.
        destruct IHb as [ξ Pξ].
        intros x Hx; apply (H x); lia. 
        destruct (H b) as [w Hw]; [lia|].
        exists (fun i => if (eq_nat_dec i b) then w else (ξ i)).
        intros; destruct (eq_nat_dec x b) as [->| eH]; [easy|].
        eapply Pξ; lia.  
    Qed.

    Lemma im_bounded_sub_form ρ ρ' φ k: bounded k φ -> ρ ⊆[k] ρ' -> 
        exists σ, (M ⊨[ρ] φ <-> M ⊨[ρ'] φ[σ]) /\ (forall x, x < k -> (σ >> (eval M interp' ρ')) x = ρ x).
    Proof.
        intros H H'.
        destruct (@im_bounded_sub _ _ _ H') as [ξ Hξ].
        exists (fun x => $ (ξ x)); split.
        - rewrite sat_comp.  
        apply bound_ext with k. exact H.
        intros. cbn. now apply Hξ.
        -  cbn. intros x Hx. now rewrite Hξ.
    Qed.

    Lemma bounded_sub_impl_henkin_env ρ ρ' ρ_s: 
        ρ' ⇒ ρ_s -> forall φ k, bounded k φ -> ρ ⊆[k] ρ' -> 
        ρ ⇒[φ] ρ_s.
    Proof.
        intros Rρ' φ k H Ink.
        assert (bounded k (∀ φ)) as HS.
        apply bounded_S_quant.
        apply (bounded_up H); lia.
        destruct (im_bounded_sub_form HS Ink ) as (σ & fH & EH).
        destruct (Rρ' (φ[up σ])) as [P _].
        split.
        + intro Hp; rewrite fH.
        apply P; revert Hp.
        intros H' n'.
        rewrite sat_comp.
        unshelve eapply (bound_ext _ H). exact (ρ_s n' .: ρ). 
        intros n Ln. 
        destruct n; cbn. {easy. }
        rewrite <- EH.
        now rewrite (cons_w ρ ρ' σ (ρ_s n')).
        lia.
        apply H'.
        + assert (bounded k (∃ φ)) as HS'.
        apply bounded_S_quant.
        apply (bounded_up H); lia.
        destruct (im_bounded_sub_form HS' Ink ) as (σ' & fH' & EH').
        specialize (Rρ' (φ[up σ'])) as [_ P'].
        rewrite fH'; intro Hp.
        destruct (P' Hp) as [w Hw].
        apply P' in Hp. 
        exists w; revert Hw; rewrite sat_comp.
        apply (bound_ext _ H).
        intros x HL.
        induction x. cbn. easy. cbn. 
        rewrite <- EH'.
        now rewrite (cons_w ρ ρ' σ' (ρ_s w)).
        lia.
    Qed.

End Technical_lemma.

Section Recursive_def.

    Variable F: nat -> nat -> M.
    Hypothesis path: forall n, F n ⇒ F (S n) /\ F n ⊆ F (S n).

    Lemma mono_F' a b: F a ⊆ F (a + b) .
    Proof.
        induction b.
        - assert (a + 0 = a) as -> by lia; apply refl_sub.
        - assert (a + S b = S(a + b)) as -> by lia.
          eapply trans_sub. exact IHb. apply path.
    Qed.

    Lemma mono_F a b: a < b -> F a ⊆ F b.
    Proof.
        assert (a < b -> Σ c, a + c = b) .
        intro H; exists (b - a); lia.
        intro aLb.
        destruct (H aLb) as [c Pc].
        specialize (mono_F' a c).
        now rewrite Pc. 
    Qed.

    Opaque encode_p. 

    Definition ι x := F (π__1 x) (π__2 x).

    Lemma ι_incl n: F n ⊆ ι.
    Proof.
        intro x; exists (encode n x); cbn.
        unfold ι.
        now rewrite cantor_left, cantor_right.
    Qed.

    Lemma ι_succ n: F n ⇒ ι.
    Proof.
        split; intros; destruct (path n) as [P _];
        destruct (P φ) as [H1 H2];
        specialize (ι_incl (S n)) as Pws.
        - apply H1.
          intro n'; destruct (Pws n') as [w ->]. 
          apply H.
        - destruct (H2 H) as [w Hw].
          destruct (Pws w) as [x ->] in Hw.
          now exists x.
    Qed.

    Lemma bounded_sub b: 
        exists E: nat, ι ⊆[b] (F E).
    Proof.
        destruct (bounded_cantor b) as [E PE].
        exists E; intros x H.
        unfold ι.
        specialize (PE _ H).
        specialize (mono_F  PE) as H1.
        destruct (H1 (π__2 x)) as [w Hw].
        now exists w.
    Qed.

    Fact Fixed_point': ι ⊆ ι.
    Proof.
        apply refl_sub.
    Qed.

    Theorem Fixed_point: ι ⇒ ι.
    Proof.
        intros.
        destruct (find_bounded φ) as [b bφ].
        destruct (bounded_sub b) as [E P].
        unshelve eapply bounded_sub_impl_henkin_env; [exact (F E) |exact b|..]; try easy.
        apply (ι_succ E).
    Qed.

End Recursive_def.

Section From_BDP_and_DC.

    Hypothesis BDP: BDP.
    Hypothesis BDP': BDP'.
    Hypothesis DC: DC.
    Variable phi_ : nat -> form.
    Variable nth_ : form -> nat.
    Hypothesis Hphi : forall phi,  phi_ (nth_ phi) = phi.

    Theorem CAC: CAC.
     Proof.
       intros A R H0.
       set (R' (p q:nat*A) := fst q = S (fst p) /\ R (fst p) (snd q)).
       destruct (H0 0) as (y0,Hy0).
       specialize (DC_with_root DC) as DC'.
       destruct (@DC' (prod nat A)) with(R:=R') (w:=(0,y0)) as (f,(Hf0,HfS)).
       - intro x; destruct (H0 (fst x)) as (y,Hy).
         exists (S (fst x),y).
         red. auto.
       - assert (Heq:forall n, fst (f n) = n).
         + induction n.
           * rewrite Hf0; reflexivity.
           * specialize HfS with n; destruct HfS as (->,_); congruence.
         + exists (fun n _ => snd (f (S n))).
           intro n'. specialize HfS with n'.
           destruct HfS as (_,HR).
           rewrite Heq in HR.
           exists tt; assumption.
     Qed.

    Definition AC_form: AC_form.
    Proof.
        intros A R total_R.
        set (R' n := R (phi_ n)).
        assert (forall x, exists y, R' x y) as total_R'. intro x. 
        now destruct (total_R (phi_ x)) as [b Pb]; exists b.
        destruct (CAC total_R') as [f Pf].
        exists (fun fm => f (nth_ fm)).
        intro x; specialize (Pf (nth_ x)).
        unfold R' in Pf.
        now rewrite (Hphi x) in Pf.
    Qed.
    
    Definition universal_witness:
        forall ρ, exists (W: nat -> M), forall φ, (forall w, M ⊨[W w.:ρ] φ) -> M ⊨[ρ] ∀ φ.
    Proof.
        intros ρ.
        destruct (@AC_form (nat -> M) (fun phi h => (forall w, M ⊨[(h w) .: ρ] phi) -> M ⊨[ρ] (∀ phi))) as [F PF].
        - intro φ; destruct (BDP (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
          exact (ρ O). exists w; intro Hx; cbn; now apply Hw.
        - exists (fun (n: nat) => F (phi_ (π__1 n)) tt (π__2 n)).
          intro φ; specialize (PF φ).
          intro H'. destruct PF as [[] PF]; apply PF.
          intro w.
          specialize (H' (encode (nth_ φ) w)).
          rewrite cantor_left, cantor_right in H'.
          now rewrite (Hphi φ) in H'.
    Qed.

    Definition existential_witness:
        forall ρ, exists (W: nat -> M), forall φ, M ⊨[ρ] (∃ φ) -> (exists w, M ⊨[W w.:ρ] φ).
    Proof.
        intros ρ.
        destruct (@AC_form (nat -> M) (fun phi h =>  M ⊨[ρ] (∃ phi) -> (exists w, M ⊨[(h w) .: ρ] phi))) as [F PF].
        - intro φ; destruct (BDP' (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
          exact (ρ O). exists w; intro Hx; cbn; now apply Hw.
        - exists (fun (n: nat) => F (phi_ (π__1 n)) tt (π__2 n)).
          intro φ; specialize (PF φ).
          intro H'. destruct PF as [[] PF]. 
          destruct (PF H') as [w Pw].
          exists (encode (nth_ φ) w).
          rewrite cantor_left, cantor_right.
          now rewrite (Hphi φ).
    Qed.

    Lemma Henkin_witness:
        forall ρ, exists (W: nat -> M), 
            (forall φ, (forall w, M ⊨[W w.:ρ] φ) -> M ⊨[ρ] ∀ φ)  
                /\ 
            (forall φ, M ⊨[ρ] (∃ φ) -> (exists w, M ⊨[W w.:ρ] φ)).
    Proof.
        intros ρ.
        destruct (universal_witness ρ) as [Uw PUw].
        destruct (existential_witness ρ) as [Ew PEw].
        exists (fun n => match EO_dec n with 
        | inl L => Uw (projT1 L)
        | inr R => Ew (projT1 R)
        end ); split.
        - intros φ Hφ.
        apply PUw; intro w.
        specialize (Hφ (2*w)).
        assert (even (2*w)) by (exists w; lia).
        destruct (EO_dec (2*w)) eqn: E'.
        enough (pi1 e = w) as <- by easy.
        destruct e; cbn; lia.
        now exfalso; apply (@EO_false (2*w)).
        - intros φ Hw%PEw.
        destruct Hw as [w Pw].
        exists (2*w + 1).
        assert (odd (2*w + 1)) by (exists w; lia).
        destruct (EO_dec (2*w + 1)) eqn: E'.
        now exfalso; apply (@EO_false (2*w + 1)).
        enough (pi1 o = w) as -> by easy.
        destruct o; cbn; lia.
    Qed.
        
    Lemma totality_Henkin: 
        forall ρ, exists ρ_s, ρ ⇒ ρ_s /\ ρ ⊆ ρ_s.
    Proof.
        intro ρ.
        destruct (Henkin_witness ρ) as [W [P1 P2]].
        exists (fun n => match EO_dec n with 
        | inl L => ρ (projT1 L)
        | inr R => W (projT1 R)
        end ); split; [split|].
        - specialize (P1 φ) as Pw.
        intros H' w'.
        apply Pw; intro w.
        assert (odd (2 * w + 1)) by (exists w; lia).
        destruct (EO_dec (2 * w + 1)) eqn: E.
        now exfalso; apply (@EO_false (2*w + 1)).
        specialize (H' (2*w + 1)).
        rewrite E in H'.
        specialize (projT2 o) as H_; cbn in H_.
        enough (pi1 o = w) as <- by easy.
        now enough ( (w + (w + 0)) + 1 = (pi1 o + (pi1 o + 0)) + 1) by lia.
        - specialize (P2 φ) as Pw.
        intros H'%Pw.
        destruct H' as [w Hw].
        exists (2*w + 1).
        assert (odd (2 * w + 1)) by (exists w; lia).
        destruct (EO_dec (2 * w + 1)) eqn: E.
        now exfalso; apply (@EO_false (2*w + 1)).
        specialize (projT2 o) as H_; cbn in H_.
        enough (pi1 o = w) as -> by easy.
        now enough ( (w + (w + 0)) + 1 = (pi1 o + (pi1 o + 0)) + 1) by lia.
        - intro x; exists (2*x). destruct (EO_dec (2 * x)) eqn: E.
        destruct e; cbn; enough (x = x0) as -> by easy; nia.
        exfalso; eapply (@EO_false (2*x)); split; [now exists x| easy].  
    Qed.

    Theorem path_ex:
        exists F: nat -> (env M), forall n, F n ⇒ F (S n) /\ F n ⊆ F (S n).
    Proof.
        eapply (@DC (env M) (fun x y => x ⇒ y /\ x ⊆ y)).
        apply totality_Henkin.
    Qed.

End From_BDP_and_DC.

End AnyModel.

Section Result.

    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Variable phi_: nat -> form.
    Variable nth_: form -> nat.
    Hypothesis Hphi: forall phi, phi_ (nth_ phi) = phi.

    Theorem LS_downward: 
        BDP -> BDP' -> DC -> forall (M: model), 𝕋 ⪳ M.
    Proof.
        intros BDP BDP' DC M.
        specialize (DC_with_root DC) as DC'.
        destruct (path_ex BDP BDP' DC Hphi) as [F PF].
        pose (Fixed_point PF) as Succ.
        specialize Henkin_env_el with (phi_ := phi_) (h := ι F) as [N PN].
        { now intro phi; exists (nth_ phi); rewrite Hphi. }
        split; intros φ; [apply (Succ φ)| apply (Succ φ)].
        now exists N, (morphism (ι F)).
    Qed.


End Result.