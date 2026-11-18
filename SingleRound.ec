require import AllCore List FSet StdBigop WeightedQuorum.
import Bigint.BIA.

(* (action, authenticated source, recipient, phase, block).
   Action 0 publishes, 1 delivers, and 2 decides. Phase 0 is a proposal,
   1 a prevote, and 2 a precommit. A publication has no recipient. *)
type event = int * int * int * int * int.
type history = event list.
op published (i phase v : int) : event = (0,i,0,phase,v).
op delivered (i p phase v : int) : event = (1,i,p,phase,v).
op decision (p v : int) : event = (2,p,0,0,v).
op empty_history : history = [].

(* Each node's inbox is the projection of delivery events to its address.
   The list can contain replays, but the support of a tally is a set. *)
op voters (ids : int list) (s : history) (p phase v : int) : int fset =
  oflist (filter (fun i => delivered i p phase v \in s) ids).
op tally (ids : int list) (stake : int -> int) (s : history) (p phase v : int) : int =
  weight ids stake (voters ids s p phase v).
op enough (ids : int list) (stake : int -> int) (s : history) (p phase v : int) : bool =
  2 * total ids stake < 3 * tally ids stake s p phase v.
op has_published (s : history) (i phase : int) : bool =
  has (fun (m : event) => m.`1 = 0 /\ m.`2 = i /\ m.`4 = phase) s.
op has_decided (s : history) (p : int) : bool =
  has (fun (m : event) => m.`1 = 2 /\ m.`2 = p) s.
op honest (ids : int list) (bad : int fset) (i : int) : bool =
  i \in ids /\ i \notin bad.

op enabled (ids : int list) (stake : int -> int) (bad : int fset)
    (proposal : int * int) (s : history) (e : event) : bool =
  let (kind,i,p,phase,v) = e in
  if kind = 0 then
    i \in ids /\ p = 0 /\
    (if phase = 0 then i = proposal.`1 /\ (i \in bad \/ (v = proposal.`2 /\ !has_published s i 0))
     else if phase = 1 then i \in bad \/
       (!has_published s i 1 /\ delivered proposal.`1 i 0 v \in s)
     else phase = 2 /\ (i \in bad \/
       (!has_published s i 2 /\ delivered proposal.`1 i 0 v \in s /\
        enough ids stake s i 1 v)))
  else if kind = 1 then
    i \in ids /\ honest ids bad p /\ published i phase v \in s
  else kind = 2 /\ honest ids bad i /\ p = 0 /\ phase = 0 /\
    !has_decided s i /\ delivered proposal.`1 i 0 v \in s /\ enough ids stake s i 2 v.

op advance (ok : bool) (s : history) (e : event) : history = if ok then e :: s else s.
op step ids stake bad leader s e = advance (enabled ids stake bad leader s e) s e.

lemma votersP ids s p phase v i :
  i \in voters ids s p phase v <=> i \in ids /\ delivered i p phase v \in s.
proof. by rewrite /voters mem_oflist mem_filter andbC. qed.

lemma enough_quorum ids stake s p phase v :
  enough ids stake s p phase v <=> quorum ids stake (voters ids s p phase v).
proof.
rewrite /quorum /enough /tally.
have sv : voters ids s p phase v \subset oflist ids.
- apply/subsetP => i; by rewrite votersP mem_oflist => -[].
by rewrite sv.
qed.

lemma publication_seen s i phase v :
  published i phase v \in s => has_published s i phase.
proof.
move=> hin; apply/hasP; exists (published i phase v).
by rewrite hin /published.
qed.

lemma honest_precommit_guard ids stake bad leader s i v :
  i \notin bad => enabled ids stake bad leader s (published i 2 v) =>
  !has_published s i 2.
proof. by move=> hb; rewrite /enabled /published /= hb /= => -[_ []]. qed.

lemma delivery_guard ids stake bad leader s i p phase v :
  enabled ids stake bad leader s (delivered i p phase v) => published i phase v \in s.
proof. by rewrite /enabled /delivered /= => -[_ [_ hp]]. qed.

lemma decision_guard ids stake bad leader s p v :
  enabled ids stake bad leader s (decision p v) => enough ids stake s p 2 v.
proof. by rewrite /enabled /decision /= => -[_ [_ [_ hq]]]. qed.

(* Histories are newest-first. A fresh honest precommit cannot follow
   an earlier precommit by that same origin, even for the same value. *)
lemma honest_precommit_once ids stake bad leader s i x y :
  i \notin bad => published i 2 x \in s =>
  !enabled ids stake bad leader s (published i 2 y).
proof.
move=> hb hin; apply/negP => he.
by move: (honest_precommit_guard ids stake bad leader s i y hb he);
  rewrite (publication_seen s i 2 x hin).
qed.

op authenticated (s : history) : bool =
  forall i p phase v, delivered i p phase v \in s => published i phase v \in s.
op single_precommit (bad : int fset) (s : history) : bool =
  forall i x y, i \notin bad => published i 2 x \in s => published i 2 y \in s => x = y.
op certified (ids : int list) (stake : int -> int) (s : history) : bool =
  forall p v, decision p v \in s => exists q,
    quorum ids stake q /\ (forall i, i \in q => published i 2 v \in s).
op safe ids stake bad s = authenticated s /\ single_precommit bad s /\ certified ids stake s.

lemma step_authenticated ids stake bad leader s e : authenticated s =>
  authenticated (step ids stake bad leader s e).
proof.
move=> ha; rewrite /step /advance.
case (enabled ids stake bad leader s e) => he // i p phase v /=.
case (delivered i p phase v = e) => hd.
- move: he; rewrite -hd => he _; right; exact (delivery_guard _ _ _ _ _ _ _ _ _ he).
- move=> hin; right; exact (ha i p phase v hin).
qed.

lemma step_single_precommit ids stake bad leader s e : single_precommit bad s =>
  single_precommit bad (step ids stake bad leader s e).
proof.
move=> hs; rewrite /step /advance.
case (enabled ids stake bad leader s e) => he // i x y hb /=.
case (published i 2 x = e) => hxe; case (published i 2 y = e) => hye /=.
- by move: hye; rewrite -hxe /published /= eq_sym.
- move=> hy; move: he; rewrite -hxe => he.
  by move: (honest_precommit_once ids stake bad leader s i y x hb hy); rewrite he.
- move=> hx; move: he; rewrite -hye => he.
  by move: (honest_precommit_once ids stake bad leader s i x y hb hx); rewrite he.
- exact (hs i x y hb).
qed.

lemma step_certified ids stake bad leader s e : authenticated s => certified ids stake s =>
  certified ids stake (step ids stake bad leader s e).
proof.
move=> ha hc; rewrite /step /advance.
case (enabled ids stake bad leader s e) => he // p v /=.
case (decision p v = e) => hd /=.
- move: he; rewrite -hd => he; exists (voters ids s p 2 v); split.
  + apply/enough_quorum; exact (decision_guard _ _ _ _ _ _ _ he).
  + move=> i; rewrite votersP => -[_ hdel]; right.
    exact (ha i p 2 v hdel).
- move=> h; case: (hc p v h) => q [hq hsent].
  exists q; split => // i hi; right; exact (hsent i hi).
qed.

lemma empty_history_safe ids stake bad : safe ids stake bad empty_history.
proof. by rewrite /safe /authenticated /single_precommit /certified /empty_history. qed.

lemma step_safe ids stake bad leader s e : safe ids stake bad s =>
  safe ids stake bad (step ids stake bad leader s e).
proof.
move=> [ha [hs hc]]; split; first exact (step_authenticated _ _ _ _ _ _ ha).
split; first exact (step_single_precommit _ _ _ _ _ _ hs).
exact (step_certified _ _ _ _ _ _ ha hc).
qed.

lemma trace_safe ids stake bad leader events :
  safe ids stake bad (foldl (step ids stake bad leader) empty_history events).
proof.
have preserve : forall s, safe ids stake bad s =>
  safe ids stake bad (foldl (step ids stake bad leader) s events).
- elim: events => [|e es ih] //=.
  move=> s hs; apply ih.
  exact (step_safe _ _ _ _ _ _ hs).
exact (preserve empty_history (empty_history_safe ids stake bad)).
qed.

lemma same_round_agreement ids stake bad leader events p p' x y :
  uniq ids => (forall i, i \in ids => 0 < stake i) =>
  3 * weight ids stake bad < total ids stake =>
  let s = foldl (step ids stake bad leader) empty_history events in
  decision p x \in s => decision p' y \in s => x = y.
proof.
move=> _ pos hb /= hx hy.
case: (trace_safe ids stake bad leader events) => _ [hs hc].
case: (hc p x hx) => a [qa ha]; case: (hc p' y hy) => b [qb hbb].
exact (certificate_unique ids stake bad a b
  (fun i v => published i 2 v \in foldl (step ids stake bad leader) empty_history events)
  x y pos hb qa qb hs ha hbb).
qed.

(* Executable configuration and unfolding rules for the UC DSL interpreter. *)
op stake_at (weights : (int * int) list) (i : int) : int =
  with weights = [] => 0
  with weights = w :: ws => if w.`1 = i then w.`2 else stake_at ws i.

op configured ids weights corrupt leader =
  uniq ids /\ leader \in ids /\ all (fun i => i \in ids) corrupt /\
  all (fun i => 0 < stake_at weights i) ids /\
  3 * weight ids (stake_at weights) (oflist corrupt) < total ids (stake_at weights).

lemma configured_agreement ids weights bad leader candidate events p p' x y :
  configured ids weights bad leader =>
  let s = foldl (step ids (stake_at weights) (oflist bad) (leader,candidate)) empty_history events in
  decision p x \in s => decision p' y \in s => x = y.
proof.
move=> [uq [_ [_ [/allP pos bound]]]] /=.
exact (same_round_agreement ids (stake_at weights) (oflist bad) (leader,candidate)
  events p p' x y uq pos bound).
qed.

lemma replay_voters ids s origin recipient phase value p k v :
  delivered origin recipient phase value \in s =>
  voters ids (delivered origin recipient phase value :: s) p k v = voters ids s p k v.
proof.
move=> h; apply/fsetP => i; rewrite !votersP /=.
case (delivered i p k v = delivered origin recipient phase value) => // he.
by rewrite he h.
qed.

lemma eval_published i phase v : published i phase v = ((0,i,0,phase,v)).
proof. by rewrite /published. qed.

lemma eval_delivered i p phase v : delivered i p phase v = ((1,i,p,phase,v)).
proof. by rewrite /delivered. qed.

lemma eval_decision p v : decision p v = ((2,p,0,0,v)).
proof. by rewrite /decision. qed.

lemma eval_empty_history  : empty_history = ([]).
proof. by rewrite /empty_history. qed.

lemma eval_voters ids s p phase v : voters ids s p phase v = (oflist (filter (fun i => delivered i p phase v \in s) ids)).
proof. by rewrite /voters. qed.

lemma eval_tally ids stake s p phase v : tally ids stake s p phase v = (weight ids stake (voters ids s p phase v)).
proof. by rewrite /tally. qed.

lemma eval_enough ids stake s p phase v : enough ids stake s p phase v = (2 * total ids stake < 3 * tally ids stake s p phase v).
proof. by rewrite /enough. qed.

lemma eval_has_published s i phase : has_published s i phase = (has (fun (m : event) => m.`1 = 0 /\ m.`2 = i /\ m.`4 = phase) s).
proof. by rewrite /has_published. qed.

lemma eval_has_decided s p : has_decided s p = (has (fun (m : event) => m.`1 = 2 /\ m.`2 = p) s).
proof. by rewrite /has_decided. qed.

lemma eval_honest ids bad i : honest ids bad i = (i \in ids /\ i \notin bad).
proof. by rewrite /honest. qed.

lemma eval_enabled ids stake bad leader s e : enabled ids stake bad leader s e = (let proposal = leader in
  let (kind,i,p,phase,v) = e in
  if kind = 0 then
    i \in ids /\ p = 0 /\
    (if phase = 0 then i = proposal.`1 /\ (i \in bad \/ (v = proposal.`2 /\ !has_published s i 0))
     else if phase = 1 then i \in bad \/
       (!has_published s i 1 /\ delivered proposal.`1 i 0 v \in s)
     else phase = 2 /\ (i \in bad \/
       (!has_published s i 2 /\ delivered proposal.`1 i 0 v \in s /\
        enough ids stake s i 1 v)))
  else if kind = 1 then
    i \in ids /\ honest ids bad p /\ published i phase v \in s
  else kind = 2 /\ honest ids bad i /\ p = 0 /\ phase = 0 /\
    !has_decided s i /\ delivered proposal.`1 i 0 v \in s /\ enough ids stake s i 2 v).
proof. by rewrite /enabled. qed.

lemma eval_advance ok s e : advance ok s e = (if ok then e :: s else s).
proof. by rewrite /advance. qed.

lemma eval_step ids stake bad leader s e : step ids stake bad leader s e = (advance (enabled ids stake bad leader s e) s e).
proof. by rewrite /step. qed.

lemma eval_weight ['a] (ids : 'a list) stake q : weight ids stake q = (big (mem q) stake ids).
proof. by rewrite /weight. qed.

lemma eval_total ['a] (ids : 'a list) stake : total ids stake = (big predT stake ids).
proof. by rewrite /total. qed.

lemma eval_configured ids weights corrupt leader : configured ids weights corrupt leader = (uniq ids /\ leader \in ids /\ all (fun i => i \in ids) corrupt /\
  all (fun i => 0 < stake_at weights i) ids /\
  3 * weight ids (stake_at weights) (oflist corrupt) < total ids (stake_at weights)).
proof. by rewrite /configured. qed.

lemma eval_stake_nil i : stake_at [] i = 0.
proof. done. qed.

lemma eval_stake_cons w ws i : stake_at (w :: ws) i =
  (if w.`1 = i then w.`2 else stake_at ws i).
proof. done. qed.

lemma eval_big_nil (p : int -> bool) w : big p w [] = 0.
proof. by rewrite big_nil. qed.

lemma eval_predT (i : int) : predT i = true.
proof. done. qed.

hint rewrite round_eval :
  eval_published
  eval_delivered
  eval_decision
  eval_empty_history
  eval_voters
  eval_tally
  eval_enough
  eval_has_published
  eval_has_decided
  eval_honest
  eval_enabled
  eval_advance
  eval_step
  eval_weight
  eval_total
  eval_configured
  eval_stake_nil eval_stake_cons eval_big_nil eval_predT big_cons mem_oflist.
