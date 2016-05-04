
Require Import Arith List Omega.

(** * Skew Binary Numbers, and application to Fast-Access Lists *)

(** Pierre Letouzey, (c) 2016. Version 1.0 9/2/2015 *)

(** This file is compatible with Coq 8.4 or 8.5. *)

(** Source: Okasaki's book "Purely Functional Data Structures". *)

(* Nota: all comments except this one are in CoqDoc syntax,
   hence the leading **, and the first [  ] around all Coq elements. *)


(** ** Misc Coq setup *)

(** Notations [[]] for [nil] and [[a;b;c]] for [a::b::nil] : *)
Import ListNotations.

(** Some compatibility between Coq 8.4 and Coq 8.5 : *)
Require Import NPeano.
Infix "=?" := Nat.eqb.
Set Asymmetric Patterns.

(** Some customizations of the [auto] tactic : *)
Hint Extern 10 (@eq nat _ _) => omega.
Hint Extern 10 (_ <= _) => omega.
Hint Extern 10 (_ < _) => omega.

(** A short alias for the [inversion] tactic : *)
Ltac inv := inversion 1; subst; simpl; auto.



(** ** PART I : Skew Binary Numbers *)

(** *** Definition of decompositions *)

(** [ones n] is the natural number with [n] times the digit 1,
    that is [2^n - 1]. Using a direct recursive definition helps
    in some proofs below. *)
Fixpoint ones n :=
 match n with
 | 0 => 0
 | S n => 2 * ones n + 1
 end.

(*Axiom not_null_ones n : *) 

(** Some properties of [ones] *)

Lemma ones_pow n : ones n = 2^n-1.
Proof.
induction n.
 - simpl. reflexivity.
 - simpl. rewrite IHn. rewrite <- !plus_n_O. admit.
Qed.


Lemma ones_pos n : 0 < n -> 0 < ones n.
Proof.
intros. induction H.
 - simpl. firstorder.
 - rewrite IHle. simpl. firstorder.
Qed.

Lemma ones_le_mono n m : n <= m -> ones n <= ones m.
Proof.
intros. induction H.
 - reflexivity.
 - rewrite IHle. simpl. firstorder.
Qed.

Lemma ones_lt_mono n m : n < m -> ones n < ones m.
Proof.
intros. induction H.
 - simpl. firstorder.
 - rewrite IHle. simpl. firstorder.
Qed.


(** [sum_ones [a;b;...]] is the sum [(2^a-1)+(2^b-1)+...].
    If [n] is the obtained numbers, we say that the list
    [[a;b;...]] is a skew binary decomposition of [n]. *)
Fixpoint sum_ones l :=
  match l with
  | nil => 0
  | n :: l' => ones n + sum_ones l'
  end.

(** Some properties of [sum_ones] *)

Lemma sum_ones_app l l' :
 sum_ones (l++l') = sum_ones l + sum_ones l'.
Proof.
induction l.
 - simpl. reflexivity.
 - simpl. rewrite IHl. firstorder.
Qed.


Lemma sum_ones_rev l :
  sum_ones (rev l) = sum_ones l.
Proof.
induction l.
 - simpl. reflexivity.
 - simpl. rewrite sum_ones_app. simpl. firstorder.
Qed.


(** *** Canonical decompositons *)

(** Not all decompositions of [n] are interesting. For instance,
    the decomposition [1;1;...;1] always exists, but is quite
    boring. And a [0] in a decomposition doesn't add anything.
    We'll now consider the canonical decompositions of the form
    [[a;b;c;d;...]] with [0<a<=b<c<d<...] :
    all factors in these decompositions are strictly positive, and
    only the smallest factor may be repeated (at most twice),
    all the other factors appear only once.
    This is expressed by the [Skew] predicate below. It uses
    the [Incr] predicate that expresses that a list is strictly
    increasing. *)

Inductive Incr : list nat -> Prop :=
 | IncrNil : Incr []
 | IncrOne n : Incr [n]
 | IncrCons n m l : n < m -> Incr (m::l) -> Incr (n :: m :: l).

Inductive Skew : list nat -> Prop :=
 | SkewNil : Skew []
 | SkewOne n : 0 < n -> Skew [n]
 | SkewCons n m l : 0 < n <= m -> Incr (m :: l) -> Skew (n::m::l).

Hint Constructors Skew Incr.

Lemma skew_examples : Skew [2;2;5;7] /\ Skew [1;2;3].
Proof.
 auto.
Qed.


(** Some properties of the [Skew] and [Incr] predicates *)

Lemma Incr_Skew m l : Incr (m::l) -> 0 < m -> Skew (m::l).
Proof. 
inv.
Qed.


Lemma Skew_inv n l : Skew (n::l) -> Skew l.
Proof.
inv. 
apply Incr_Skew. 
 - assumption. 
 - auto.
Qed.


(** The main result is now that any natural number admits one
    and only one canonical skew binary decomposition. *)


(** *** Existence *)

(** For the "exist" part of the statement, we can even build
    the decomposition of [n+1] explicitely out of the
    decomposition of [n]. *)

(** Nota: the syntax [n =? m] is a boolean equality test [Nat.eqb].
    For reasoning about it, you can do a [case Nat.eqb_spec] when
    your goal contains a [=?]. *)

Definition next l :=
  match l with
  | n::m::l' => if n =? m then (S n) :: l' else 1::l
  | _ => 1::l
  end.


Lemma next_sum l : sum_ones (next l) = S (sum_ones l).
Proof.
induction l.
 - simpl. reflexivity.
 - Admitted.


Lemma next_skew l : Skew l -> Skew (next l).
Proof.
inversion 1. subst.
 - simpl. auto.
 - simpl. auto.
 - subst. 
Admitted.


(** So the decomposition of [n] is obtained by repeating
    [n] times the [next] function. *)

Fixpoint iter_next n :=
 match n with
 | 0 => nil
 | S n => next (iter_next n)
 end.


Lemma iter_next_sum n : sum_ones (iter_next n) = n.
Proof.
induction n.
 - simpl. reflexivity.
 - simpl. rewrite !next_sum. f_equal. assumption. 
Qed.

Lemma iter_next_skew n : Skew (iter_next n).
Proof.
induction n.
 - simpl. auto.
 -
Admitted.

(** Hence the existence statement: *)

Lemma decomp_exists : forall n, exists l, sum_ones l = n /\ Skew l.
Proof.
induction n.
 - exists []. simpl. firstorder.
 -
Admitted.



(** *** Reversed canonical decomposition *)

(** For the unicity of the decomposition, we have to study the
    largest factor. For that, it is quite easier to consider
    a decomposition sorted in decreasing order : the largest
    factor will come first in the list.
    The [Weks] predicate is equivalent to [Skew] on the mirror
    list. Its definition is standalone, but we'll also need
    later a [Decr] predicate stating that a list is strictly
    decreasing. *)

Inductive Weks : list nat -> Prop :=
 | WeksNil : Weks []
 | WeksOne n : 0 < n -> Weks [n]
 | WeksTwo n : 0 < n -> Weks [n;n]
 | WeksCons n m l : m < n -> Weks (m::l) -> Weks (n::m::l).

Inductive Decr : list nat -> Prop :=
 | DecrNil : Decr []
 | DecrOne n : Decr [n]
 | DecrCons n m l : m < n -> Decr (m :: l) -> Decr (n :: m :: l).

Hint Constructors Weks Decr.


(** Let's now prove equivalences between [Skew] and [Weks]. *)

Lemma Incr_last l n m :
  Incr (l ++ [n]) -> n < m -> Incr (l++[n;m]).
Proof.
Admitted.


Lemma Decr_last l n m :
 Decr (l++[n]) -> m < n -> Decr (l++[n;m]).
Proof.
Admitted.

Lemma Incr_Decr l : Incr l -> Decr (rev l).
Proof.
inversion 1.
 - auto.
 - subst. simpl. auto.
 - subst. simpl. 
Admitted.


Lemma Skew_last l n m :
  Skew (l++[n]) -> n < m -> Skew (l++[n;m]).
Proof.
Admitted.

Lemma Weks_last l n m :
 Decr (l++[n]) -> 0 < m <= n -> Weks (l++[n;m]).
Proof.
Admitted.

Lemma Weks_Skew l : Weks l <-> Skew (rev l).
Proof.
Admitted.



(** *** Unicity *)

Lemma Weks_pos n l : Weks (n::l) -> 0 < n.
Proof.
inv.
Admitted.

(** The key property : a canonical decomposition with [n] as
    largest factor cannot exceed [ones (S n)].
    Hence two decompositions with the same sum will have the
    same largest factors. *)

Lemma sum_ones_bound n l :
  Weks (n::l) -> sum_ones (n::l) < ones (S n).
Proof.
simpl. induction l.
 - simpl. firstorder.
 - simpl.
Admitted.

Lemma decomp_unique_weks l l' : Weks l -> Weks l' ->
 sum_ones l = sum_ones l' -> l = l'.
Proof.
Admitted.

Lemma decomp_unique l l' : Skew l -> Skew l' ->
 sum_ones l = sum_ones l' -> l = l'.
Proof.
Admitted.

Lemma decomp_unique' l n :
  Skew l -> n = sum_ones l -> l = iter_next n.
Proof.
Admitted.



(** *** Decomposition of predecessor *)

(** In the same spirit as [next], we could actually build
    the decomposition of [n-1] out of the decomposition of [n].
    Note that this function is meant to be used on canonical
    decomposition, [prev (0::l)] isn't supposed to occur, we can
    answer anything in this case, here [nil]. *)

Definition prev l :=
  match l with
  | 1::l => l
  | (S n)::l => n::n::l
  | _ => nil
  end.

Lemma prev_sum l : Skew l ->
 sum_ones (prev l) = pred (sum_ones l).
Proof.
Admitted.

Lemma prev_skew l : Skew l -> Skew (prev l).
Proof.
Admitted.

(** And thanks to the unicity, we could easily prove results
    about the composition of [prev] and [next]. *)

Lemma prev_next l : Skew l -> prev (next l) = l.
Proof.
Admitted.

Lemma next_prev l : Skew l -> l<>nil -> next (prev l) = l.
Proof.
Admitted.




(** ** PART II : Some complements about Coq arithmetic and lists *)

(** *** An exact subtraction

   No rounding at zero with this one, but rather an output
   in [option nat]. Later, to prove things involving [sub_option],
   simply do a [case sub_option_spec]. *)

Fixpoint sub_option n m :=
  match n, m with
  | _, 0 => Some n
  | 0, _ => None
  | S n, S m => sub_option n m
  end.

Inductive SubOptionSpec (n m : nat) : option nat -> Prop :=
 | SubLe p : n = m + p -> SubOptionSpec n m (Some p)
 | SubLt : n < m -> SubOptionSpec n m None.
Hint Constructors SubOptionSpec.

Lemma sub_option_spec n m : SubOptionSpec n m (sub_option n m).
Proof.
Admitted.

(** *** Injectivity of list concatenation *)

Lemma app_inv {A} (u u' v v' : list A) :
 length u = length u' -> u ++ v = u' ++ v' -> u = u' /\ v = v'.
Proof.
Admitted.

(** *** Access to the n-th element of a list

   This is a cleaner version of List.nth_error. *)

Fixpoint list_nth {A} (l:list A) i : option A :=
  match i,l with
    | 0,   x::_ => Some x
    | S j, _::l => list_nth l j
    | _, _ => None
  end.

Lemma list_nth_app_l {A} (l l':list A)(n:nat) : n < length l ->
  list_nth (l++l') n = list_nth l n.
Proof.
Admitted.

Lemma list_nth_app_r {A} (l l':list A)(n:nat) :
  list_nth (l++l') (length l + n) = list_nth l' n.
Proof.
Admitted.



(** ** PART III: Skew Lists *)

Section SkewList.
Parameter A:Type.

(** Skewlists are list of trees of elements.
    We want here to store [2^d-1] elements per tree of depth [d],
    so we put data at the nodes and not at the leaves.
    The value at the root node is the head of the skewlist, then
    comes the values in the left sub-tree, then the right sub-tree. *)

(** Perfect binary trees parametrized by their depth. *)

Inductive tree : nat -> Type :=
 | Leaf : tree 0
 | Node : forall {d}, A -> tree d -> tree d -> tree (S d).

(** A [dtree] is a pair of a depth and a tree of this depth. *)

Inductive dtree := Tree : forall {d}, tree d -> dtree.

(** The type of skewlists *)

Definition skewlist := list dtree.

(** The number of elements in a skewlist *)

Definition depth (t:dtree) := let (d,_) := t in d.
Definition skew_length l := sum_ones (map depth l).

(** The invariant we impose on skewlists to keep a nice complexity: *)

Definition SkewList l := Skew (map depth l).

Hint Unfold SkewList.

(** The empty skewlist *)

Definition empty : skewlist := nil.

Lemma empty_invariant : SkewList empty.
Proof.
Admitted.

(** *** Conversion from skewlist to regular list *)

Fixpoint tree_to_list {d} (t:tree d) :=
  match t with
  | Leaf => nil
  | Node _ a tl tr => a :: tree_to_list tl ++ tree_to_list tr
  end.

Fixpoint to_list l :=
  match l with
  | nil => nil
  | Tree _ t :: l => tree_to_list t ++ to_list l
  end.


(** *** Properties of length and size of trees and skewlists *)

Fixpoint size {d} (t:tree d) :=
  match t with
  | Leaf => 0
  | Node _ a tl tr => 1 + size tl + size tr
  end.

Lemma size_ones n (t : tree n) : size t = ones n.
Proof.
Admitted.

Lemma length_tree_to_list d (t:tree d) :
 length (tree_to_list t) = size t.
Proof.
Admitted.

Lemma length_to_list l :
 length (to_list l) = skew_length l.
Proof.
Admitted.


(** *** A adhoc induction principle on two trees of same depth *)

(** When you have two trees [(t1 t2 : tree n)], you cannot simply
    do [induction t1; destruct t2], Coq will most certainly
    complain about issues with dependent types. In this case,
    you will have to use the [tree_ind2] principle defined below.
    The details of how these things are built aren't important,
    just check the type of the obtained [tree_ind2] and compare
    it to the one of the automatically generated [tree_ind].
    NB: this part is inspired by P. Boutillier's Vector library.
*)

Definition case0 (t : tree 0) :
  forall (P : tree 0 -> Prop), P Leaf -> P t :=
  match t with
  | Leaf => fun P H => H
  | _ => tt
  end.

Definition caseS {n} (t : tree (S n)) :
  forall (P : tree (S n) -> Prop),
  (forall x t1 t2, P (Node x t1 t2)) -> P t :=
  match t with
  | Node _ x t1 t2 => fun P H => H x t1 t2
  | _ => tt
  end.

Definition tree_ind2 (P : forall {n}, tree n -> tree n -> Prop)
  (base : P Leaf Leaf)
  (rec : forall {n x tl1 tr1 y tl2 tr2},
    P tl1 tl2 -> P tr1 tr2 ->
    P (Node x tl1 tr1) (Node y tl2 tr2)) :=
  fix loop {n} (t1 : tree n) : forall t2 : tree n, P t1 t2 :=
  match t1 with
  | Leaf => fun t2 => case0 t2 _ base
  | Node _ x1 tl1 tr1 => fun t2 =>
    caseS t2 (P (Node x1 tl1 tr1))
     (fun x2 tl2 tr2 => rec (loop tl1 tl2) (loop tr1 tr2))
  end.

(** *** Unicity of the skewlist representation *)

Lemma tree_unique n (t t' : tree n) :
 tree_to_list t = tree_to_list t' -> t = t'.
Proof.
Admitted.

Lemma skewlist_unique l l' : SkewList l -> SkewList l' ->
 to_list l = to_list l' -> l = l'.
Proof.
Admitted.


(** *** Coercion from [tree d] to [tree d'] when [d=d']. *)

Definition coerc {d d'} : tree d -> d = d' -> tree d'.
Proof.
 destruct 2.
 trivial.
Defined.

Lemma coerc_to_list d d' (t:tree d) (e : d = d') :
 tree_to_list (coerc t e) = tree_to_list t.
Proof.
 now destruct e.
Qed.

(** *** cons *)

(** Insert an element into a skewlist.
    Constant cost (when ignoring the cost of comparison). *)

Definition leaf := Tree Leaf.

Definition singleton x := Tree (Node x Leaf Leaf).

Definition cons x l :=
  match l with
  | Tree d1 t1 :: Tree d2 t2 :: l' =>
    match eq_nat_dec d1 d2 with
    | left E => Tree (Node x (coerc t1 E) t2) :: l'
    | right _ => singleton x :: l
    end
  | _ => singleton x :: l
  end.

Lemma cons_next x l : map depth (cons x l) = next (map depth l).
Proof.
Admitted.

Lemma cons_invariant x l : SkewList l -> SkewList (cons x l).
Proof.
Admitted.

Lemma cons_to_list x l : to_list (cons x l) = x :: to_list l.
Proof.
Admitted.


(** *** Conversion from a regular list to a skewlist

    We simply iterate [cons]. The cost is hence linear. *)

Definition from_list (l:list A) : skewlist := List.fold_right cons nil l.

Lemma cons_from_list x l : from_list (x::l) = cons x (from_list l).
Admitted.

Lemma from_list_invariant l : SkewList (from_list l).
Admitted.

Lemma to_from l : to_list (from_list l) = l.
Admitted.

Lemma unique_from_to l : SkewList l -> l = from_list (to_list l).
Admitted.



(** *** Decons : head element and rest of a skewlist, if any

    Constant cost. *)

Definition decons l :=
 match l with
 | Tree _ (Node 0 x _ _) :: l' => Some (x,l')
 | Tree _ (Node _ x tl tr) :: l' =>
   Some (x, Tree tl :: Tree tr :: l')
 | _ => None
 end.

Lemma decons_prev l x l':
 decons l = Some (x,l') -> map depth l' = prev (map depth l).
Proof.
Admitted.

Lemma decons_invariant x l l' :
 SkewList l -> decons l = Some (x,l') -> SkewList l'.
Proof.
Admitted.

Lemma decons_none l : SkewList l -> (decons l = None <-> l = nil).
Proof.
Admitted.

Lemma decons_to_list x l l' :
 decons l = Some (x,l') -> to_list l = x :: to_list l'.
Proof.
Admitted.

Lemma decons_cons x l : SkewList l -> decons (cons x l) = Some (x,l).
Proof.
Admitted.

Lemma cons_decons x l l' :
 SkewList l -> decons l = Some (x,l') -> cons x l' = l.
Proof.
Admitted.


(** *** Access to the n-th element of a skew list *)

(** n-th element of the tree t *)

Fixpoint nth_tree {d} (t : tree d) n :=
  match t with
  | Leaf => None
  | Node d x tl tr =>
    match n with
    | O => Some x
    | S n' =>
      match sub_option n' (ones d) with
      | None => nth_tree tl n'
      | Some n'' => nth_tree tr n''
      end
    end
  end.

(** n-th element of a skewlist l. *)

Fixpoint nth l n :=
  match l with
  | nil => None
  | Tree d t :: l =>
    match sub_option n (ones d) with
    | None => nth_tree t n
    | Some n' => nth l n'
    end
  end.

Lemma nth_tree_ok d (t : tree d) n :
  nth_tree t n = list_nth (tree_to_list t) n.
Proof.
Admitted.

Lemma nth_ok l n : nth l n = list_nth (to_list l) n.
Proof.
Admitted.


(** In the "real life", all the arithmetical operations on the
  sizes will be done on machine integers, and hence have a
  constant cost (for instance [ones n = (1 << n) - 1]).
  In this situation, [cons] and [decons] have really a constant
  cost and [nth] has a logarithmic cost with respect to the
  number of elements in the skew list.

  In Coq, things are not so nice, since on [nat] all arithmetic
  operations are at least linear. We could at least define
  a notion of distance of elements in the skew list, and show
  that this distance is at most logarithmic. (TODO)
*)


(** Possible extensions :
  - a [set_nth] function, such that [set_nth l n x] creates a copy
    of the skewlist [l] where the n-th element is now replaced by [x].

  - a [drop] function, such that [drop k l] is the skewlist [l]
    with its first [k] elements removed. This could be done by
    repeating [k] times the [decons] function, but with a direct
    definition we could obtain a better complexity (logarithmic
    in the size of [l], when ignoring arithmetic ops).
*)

End SkewList.
