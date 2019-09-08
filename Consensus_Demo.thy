theory
  Consensus_Demo
imports
  Network
begin

datatype 'val msg
  = Propose 'val
  | Accept 'val

fun acceptor_step where
  ‹acceptor_step state (Receive sender (Propose val)) =
     (case state of
        None   ⇒ (Some val, {Send sender (Accept val)}) |
        Some v ⇒ (Some v,   {Send sender (Accept v)}))› |
  ‹acceptor_step state _ = (state, {})›

fun proposer_step where
  ‹proposer_step None (Request val) = (None, {Send 0 (Propose val)})› |
  ‹proposer_step None (Receive _ (Accept val)) = (Some val, {})› |
  ‹proposer_step state _ = (state, {})›

fun consensus_step where
  ‹consensus_step proc =
     (if proc = 0 then acceptor_step else proposer_step)›

(* Invariant 1: for any proposer p, if p's state is ``Some val'',
   then there exists a process that has sent a message
   ``Accept val'' to p. *)

definition inv1 where
  ‹inv1 msgs states ⟷
     (∀proc val. proc ≠ 0 ∧ states proc = Some val ⟶
                 (∃sender. (sender, Send proc (Accept val)) ∈ msgs))›

(* Invariant 2: if a message ``Accept val'' has been sent, then
   the acceptor is in the state ``Some val''. *)

definition inv2 where
  ‹inv2 msgs states ⟷
     (∀sender recpt val. (sender, Send recpt (Accept val)) ∈ msgs ⟶
                         states 0 = Some val)›

lemma invariant_propose:
  assumes ‹msgs' = msgs ∪ {(proc, Send 0 (Propose val))}›
    and ‹inv1 msgs states ∧ inv2 msgs states›
  shows ‹inv1 msgs' states ∧ inv2 msgs' states›
proof -
  have ‹⋀sender proc val.
      ((sender, Send proc (Accept val)) ∈ msgs') ⟷
      ((sender, Send proc (Accept val)) ∈ msgs)›
    using assms(1) by blast
  then show ?thesis
    by (meson assms(2) inv1_def inv2_def)
qed

lemma invariant_decide:
  assumes ‹states' = states (0 := Some val)›
    and ‹msgs' = msgs ∪ {(0, Send sender (Accept val))}›
    and ‹states 0 = None›
    and ‹inv1 msgs states ∧ inv2 msgs states›
  shows ‹inv1 msgs' states' ∧ inv2 msgs' states'›
proof -
  {
    fix p v
    assume asm: ‹p ≠ 0 ∧ states' p = Some v›
    hence ‹states p = Some v›
      by (simp add: asm assms(1))
    hence ‹∃sender. (sender, Send p (Accept v)) ∈ msgs›
      by (meson asm assms(4) inv1_def)
    hence ‹∃sender. (sender, Send p (Accept v)) ∈ msgs'›
      using assms(2) by blast
  }
  moreover {
    fix p1 p2 v
    assume asm: ‹(p1, Send p2 (Accept v)) ∈ msgs'›
    have ‹states' 0 = Some v›
    proof (cases ‹(p1, Send p2 (Accept v)) ∈ msgs›)
      case True
      then show ?thesis
        by (metis assms(3) assms(4) inv2_def option.simps(3))
    next
      case False
      then show ?thesis
        using asm assms(1) assms(2) by auto
    qed
  }
  ultimately show ?thesis
    by (simp add: inv1_def inv2_def)
qed

lemma invariant_decided:
  assumes ‹msgs' = msgs ∪ {(0, Send sender (Accept val))}›
    and ‹states 0 = Some val›
    and ‹inv1 msgs states ∧ inv2 msgs states›
  shows ‹inv1 msgs' states ∧ inv2 msgs' states›
proof -
  {
    fix p v
    assume ‹p ≠ 0 ∧ states p = Some v›
    hence ‹∃sender. (sender, Send p (Accept v)) ∈ msgs›
      by (meson assms(3) inv1_def)
    hence ‹∃sender. (sender, Send p (Accept v)) ∈ msgs'›
      using assms(1) by blast
  }
  moreover {
    fix p1 p2 v
    assume asm: ‹(p1, Send p2 (Accept v)) ∈ msgs'›
    have ‹states 0 = Some v›
    proof (cases ‹(p1, Send p2 (Accept v)) ∈ msgs›)
      case True
      then show ?thesis
        by (meson assms(3) inv2_def)
    next
      case False
      then show ?thesis
        using asm assms(1) assms(2) by blast
    qed
  }
  ultimately show ‹inv1 msgs' states ∧ inv2 msgs' states›
    by (simp add: inv1_def inv2_def)
qed

lemma invariant_learn:
  assumes ‹states' = states (proc := Some val)›
    and ‹(sender, Send proc (Accept val)) ∈ msgs›
    and ‹inv1 msgs states ∧ inv2 msgs states›
  shows ‹inv1 msgs states' ∧ inv2 msgs states'›
proof -
  {
    fix p v
    assume asm: ‹p ≠ 0 ∧ states' p = Some v›
    have ‹∃sender. (sender, Send p (Accept v)) ∈ msgs›
    proof (cases ‹p = proc›)
      case True
      then show ?thesis
        using asm assms(1) assms(2) by auto
    next
      case False
      then show ?thesis
        by (metis asm assms(1) assms(3) fun_upd_apply inv1_def)
    qed
  }
  moreover {
    fix p1 p2 v
    assume ‹(p1, Send p2 (Accept v)) ∈ msgs›
    hence ‹states' 0 = Some v›
      by (metis assms fun_upd_apply inv2_def)
  }
  ultimately show ?thesis
    by (simp add: inv1_def inv2_def)
qed

lemma invariant_proposer:
  assumes ‹proposer_step (states proc) event = (new_state, sent)›
    and ‹msgs' = msgs ∪ ((λmsg. (proc, msg)) ` sent)›
    and ‹states' = states (proc := new_state)›
    and ‹execute consensus_step (λp. None) UNIV (events @ [(proc, event)]) msgs' states'›
    and ‹inv1 msgs states ∧ inv2 msgs states›
  shows ‹inv1 msgs' states' ∧ inv2 msgs' states'›
proof (cases event)
  case (Receive sender msg)
  then show ?thesis
  proof (cases msg)
    case (Propose val)
    then show ?thesis
      using Receive assms by auto
  next
    case (Accept val) (* proposer receives Accept message: learn the decided value *)
    then show ?thesis
    proof (cases ‹states proc›)
      case None
      hence ‹states' = states (proc := Some val) ∧ msgs' = msgs›
        using Accept Receive assms(1) assms(2) assms(3) by auto
      then show ?thesis
        by (metis Accept Receive assms(4) assms(5) execute_receive invariant_learn)
    next
      case (Some v)
      then show ?thesis
        using assms by auto
    qed
  qed
next
  (* on a Request event, proposer sends a Propose message if its state
     is None, or ignores the event if already learnt a decision *)
  case (Request val)
  then show ‹inv1 msgs' states' ∧ inv2 msgs' states'›
  proof (cases ‹states proc›)
    case None
    hence ‹states' = states ∧ msgs' = msgs ∪ {(proc, Send 0 (Propose val))}›
      using Request assms(1) assms(2) assms(3) by auto
    then show ?thesis
      by (simp add: assms(5) invariant_propose)
  next
    case (Some v)
    then show ?thesis using assms by auto
  qed
next
  case Timeout
  then show ‹inv1 msgs' states' ∧ inv2 msgs' states'›
    using assms by auto
qed

lemma invariant_acceptor:
  assumes ‹acceptor_step (states 0) event = (new_state, sent)›
    and ‹msgs' = msgs ∪ ((λmsg. (0, msg)) ` sent)›
    and ‹states' = states (0 := new_state)›
    and ‹execute consensus_step (λp. None) UNIV (events @ [(0, event)]) msgs' states'›
    and ‹inv1 msgs states ∧ inv2 msgs states›
  shows ‹inv1 msgs' states' ∧ inv2 msgs' states'›
proof (cases event)
  case (Receive sender msg)
  then show ‹inv1 msgs' states' ∧ inv2 msgs' states'›
  proof (cases msg)
    case (Propose val)
    then show ?thesis
    proof (cases ‹states 0›)
      case None (* not decided yet: decide now *)
      hence ‹states' = states (0 := Some val) ∧
             msgs' = msgs ∪ {(0, Send sender (Accept val))}›
        using Receive Propose assms(1) assms(2) assms(3) by auto
        (* for some reason sledgehammer couldn't find the line above *)
      then show ?thesis
        by (simp add: None assms(5) invariant_decide)
    next
      case (Some val') (* already decided previously *)
      hence ‹states' = states ∧
             msgs' = msgs ∪ {(0, Send sender (Accept val'))}›
        using Receive Propose assms(1) assms(2) assms(3) by auto
        (* for some reason sledgehammer couldn't find the line above *)
      then show ?thesis
        by (simp add: invariant_decided assms(5) Some)
    qed
  next
    case (Accept val)
    then show ?thesis
      using Receive assms by auto
  qed
next
  case (Request val)
  then show ‹inv1 msgs' states' ∧ inv2 msgs' states'›
    using assms by auto
next
  case Timeout
  then show ‹inv1 msgs' states' ∧ inv2 msgs' states'›
    using assms by auto
qed

lemma invariants:
  assumes ‹execute consensus_step (λx. None) UNIV events msgs' states'›
  shows ‹inv1 msgs' states' ∧ inv2 msgs' states'›
using assms proof(induction events arbitrary: msgs' states' rule: List.rev_induct)
  case Nil
  from this show ‹inv1 msgs' states' ∧ inv2 msgs' states'›
    using execute_init inv1_def inv2_def by fastforce
next
  case (snoc x events)
  obtain proc event where ‹x = (proc, event)›
    by fastforce
  hence exec: ‹execute consensus_step (λp. None) UNIV
               (events @ [(proc, event)]) msgs' states'›
    using snoc.prems by blast
  from this obtain msgs states sent new_state
    where step_rel1: ‹execute consensus_step (λx. None) UNIV events msgs states›
      and step_rel2: ‹consensus_step proc (states proc) event = (new_state, sent)›
      and step_rel3: ‹msgs' = msgs ∪ ((λmsg. (proc, msg)) ` sent)›
      and step_rel4: ‹states' = states (proc := new_state)›
    by auto
  have inv_before: ‹inv1 msgs states ∧ inv2 msgs states›
    using snoc.IH step_rel1 by fastforce
  then show ‹inv1 msgs' states' ∧ inv2 msgs' states'›
  proof (cases ‹proc = 0›)
    case True
    then show ?thesis
      by (metis consensus_step.simps exec inv_before invariant_acceptor
          step_rel2 step_rel3 step_rel4)
  next
    case False
    then show ?thesis
      by (metis consensus_step.simps exec inv_before invariant_proposer
          step_rel2 step_rel3 step_rel4)
  qed
qed

theorem agreement:
  assumes ‹execute consensus_step (λx. None) UNIV events msgs states›
    and ‹states proc1 = Some val1› and ‹states proc2 = Some val2›
  shows ‹val1 = val2›
proof -
  have ‹states 0 = Some val1›
    by (metis assms(1) assms(2) inv1_def inv2_def invariants)
  moreover have ‹states 0 = Some val2›
    by (metis assms(1) assms(3) inv1_def inv2_def invariants)
  ultimately show ‹val1 = val2›
    by simp
qed

end
