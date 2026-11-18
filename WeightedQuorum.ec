require import AllCore List FSet StdBigop StdOrder StdRing Ring.
import Bigint.BIA IntOrder IntID.

(* The universe is a duplicate-free enumeration of a finite validator set. *)
op weight ['a] (ids : 'a list) (stake : 'a -> int) (q : 'a fset) : int =
  big (mem q) stake ids.
op total ['a] (ids : 'a list) (stake : 'a -> int) : int =
  big predT stake ids.
op quorum ['a] (ids : 'a list) (stake : 'a -> int) (q : 'a fset) : bool =
  q \subset oflist ids /\ 2 * total ids stake < 3 * weight ids stake q.

lemma weight_union_inter ['a] (ids : 'a list) (stake : 'a -> int) (a b : 'a fset) :
  weight ids stake (a `|` b) + weight ids stake (a `&` b) =
  weight ids stake a + weight ids stake b.
proof.
elim: ids => [|x xs ih]; rewrite /weight ?big_nil // !big_cons in_fsetU in_fsetI.
rewrite /weight in ih.
case (x \in a) => ha; case (x \in b) => hb /=.
- by rewrite addrACA ih -addrACA.
- by rewrite -!addrA ih.
- by rewrite -addrA ih addrCA.
- exact ih.
qed.

lemma weight_mono ['a] (ids : 'a list) (stake : 'a -> int) (a b : 'a fset) :
  (forall i, i \in ids => 0 < stake i) => a \subset b =>
  weight ids stake a <= weight ids stake b.
proof.
move=> pos sub; elim: ids pos => [|x xs ih] pos;
  rewrite /weight ?big_nil // !big_cons.
have ge := ih _; first by move=> i hi; apply pos; rewrite /= hi.
rewrite /weight in ge.
have px : 0 < stake x by apply pos; rewrite /=.
have hs : x \in a => x \in b by move/subsetP: sub => sub; apply sub.
case (x \in a) => ha; case (x \in b) => hb /=.
- by rewrite ler_add2l.
- by rewrite (hs ha) in hb.
- apply (ler_trans _ _ _ ge); by rewrite ler_addr ltrW.
- exact ge.
qed.

lemma total_weight ['a] (ids : 'a list) (stake : 'a -> int) :
  weight ids stake (oflist ids) = total ids stake.
proof.
rewrite /weight /total big_seq; apply eq_bigl => i.
by rewrite mem_oflist.
qed.

lemma weighted_intersection ['a] (ids : 'a list) (stake : 'a -> int) (a b : 'a fset) :
  (forall i, i \in ids => 0 < stake i) => quorum ids stake a => quorum ids stake b =>
  total ids stake < 3 * weight ids stake (a `&` b).
proof.
move=> pos [sa qa] [sb qb].
have sub : a `|` b \subset oflist ids.
- apply/subsetP => i; rewrite in_fsetU => -[h|h].
  + by move/subsetP: sa => sa; apply sa.
  + by move/subsetP: sb => sb; apply sb.
have hm := weight_mono ids stake (a `|` b) (oflist ids) pos sub.
rewrite total_weight in hm.
have hi := weight_union_inter ids stake a b.
have hh := ltr_add _ _ _ _ qa qb.
have he : 3 * (weight ids stake (a `|` b) + weight ids stake (a `&` b)) =
          3 * weight ids stake a + 3 * weight ids stake b.
- rewrite hi; ring.
move: hh; rewrite -he mulzDr => hh.
have hm3 : 3 * weight ids stake (a `|` b) <= 3 * total ids stake.
- by rewrite ler_pmul2l.
have ht : 2 * total ids stake + 2 * total ids stake <
          3 * total ids stake + 3 * weight ids stake (a `&` b).
- apply (ltr_le_trans _ _ _ hh); by rewrite ler_add2r.
have hre : 2 * total ids stake + 2 * total ids stake =
          3 * total ids stake + total ids stake by ring.
move: ht; rewrite hre => ht.
by rewrite ltr_add2l in ht.
qed.

lemma honest_overlap ['a] (ids : 'a list) (stake : 'a -> int) (bad a b : 'a fset) :
  (forall i, i \in ids => 0 < stake i) => 3 * weight ids stake bad < total ids stake =>
  quorum ids stake a => quorum ids stake b =>
  exists i, i \in a /\ i \in b /\ i \notin bad.
proof.
move=> pos hb qa qb.
have hi := weighted_intersection ids stake a b pos qa qb.
case (exists i, i \in a /\ i \in b /\ i \notin bad) => // none.
have sub : a `&` b \subset bad.
- apply/subsetP => i; rewrite in_fsetI => -[ha hb'].
  case (i \in bad) => // hbad.
  apply none; by exists i.
have hm := weight_mono ids stake (a `&` b) bad pos sub.
have hm3 : 3 * weight ids stake (a `&` b) <= 3 * weight ids stake bad.
- by rewrite ler_pmul2l.
have hc := ltr_le_trans _ _ _ hi hm3.
by rewrite (ltr_gtF _ _ hb) in hc.
qed.

lemma honest_overlap_positive ['a] (ids : 'a list) (stake : 'a -> int)
    (bad a b : 'a fset) :
  (forall i, i \in ids => 0 < stake i) => 3 * weight ids stake bad < total ids stake =>
  quorum ids stake a => quorum ids stake b =>
  exists i, i \in a /\ i \in b /\ i \notin bad /\ 0 < stake i.
proof.
move=> pos hb qa qb.
case: (honest_overlap ids stake bad a b pos hb qa qb) => i [ia [ib hi]].
exists i; split=> //; split=> //; split=> //; apply pos.
case: qa => /subsetP sa _; by move: (sa i ia); rewrite mem_oflist.
qed.

lemma certificate_unique ['a 'b] (ids : 'a list) (stake : 'a -> int)
    (bad a b : 'a fset) (sent : 'a -> 'b -> bool) (x y : 'b) :
  (forall i, i \in ids => 0 < stake i) => 3 * weight ids stake bad < total ids stake =>
  quorum ids stake a => quorum ids stake b =>
  (forall i v v', i \notin bad => sent i v => sent i v' => v = v') =>
  (forall i, i \in a => sent i x) => (forall i, i \in b => sent i y) => x = y.
proof.
move=> pos hb qa qb single ha hr.
case: (honest_overlap ids stake bad a b pos hb qa qb) => i [ia [ib good]].
exact (single i x y good (ha i ia) (hr i ib)).
qed.
