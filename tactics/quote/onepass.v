(** One-pass quoting of an equation into a free structure.

  [quote_equation] in [quote.vars] quotes by typeclass search in the [quote]
  database: a first search with atom placeholders, a loop that extracts the
  atoms from that partial proof, and a second search that builds the proof.
  Here a single syntactic walk over the goal produces a tree and the atom
  list [Γ], and a fold over the tree builds the proof term directly from the
  preservation lemmas, with no search.

  A structure is described by an operation table. Each operation is a pair
  - a pattern [fun a₁ … aₙ => op a₁ … aₙ], elaborated at the goal's carrier,
    so that it is syntactically the operation as it appears in the goal;
  - a lemma head [fun Γ => let ev := eval Γ in
      fun x₁ y₁ … xₙ yₙ (p₁ : quote ev x₁ y₁) … (pₙ : quote ev xₙ yₙ) =>
        (proof of quote ev (op x₁ … xₙ) (op y₁ … yₙ))].
  Patterns are matched first-order and up to universe instances. Subterms
  that match no pattern are atoms, identified syntactically.

  Lemma heads are elaborated by Ltac1, which inserts coercions (see
  [try_all_hyps] for why Ltac2 cannot). [Γ] and [ev] are posed once, so the
  proof term binds them with [let]; each node of the certificate is the
  lemma applied to its arguments, obtained by substitution, and the
  free-side term of each node is read off a template computed once per
  lemma, so the fold does no retyping. *)

Require Import prelude.
Require Import abstract_algebra logic.aprop nat list.
Require Export quote.base quote.vars.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Module onepass.

Ltac2 fail_msg (s : string) : 'a :=
  Control.throw (Tactic_failure (Some (Message.of_string s))).

Ltac2 mk_app (f : constr) (args : constr list) : constr :=
  match args with
  | [] => f
  | _ => Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list args))
  end.

Ltac2 rec lam_count (t : constr) : int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Lambda _ b => Int.add 1 (lam_count b)
  | _ => 0
  end.

Ltac2 rec lam_body (n : int) (t : constr) : constr :=
  if Int.equal n 0 then t else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Lambda _ b => lam_body (Int.sub n 1) b
  | _ => fail_msg "onepass: too few binders"
  end.

Ltac2 rec prod_body (n : int) (t : constr) : constr :=
  if Int.equal n 0 then t else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ b => prod_body (Int.sub n 1) b
  | _ => fail_msg "onepass: too few products"
  end.

(** [fun Γ => let ev := e in body] at [Γ := g], [ev := v] *)
Ltac2 inst_env (lam : constr) (g : constr) (v : constr) : constr :=
  match Constr.Unsafe.kind lam with
  | Constr.Unsafe.Lambda _ body =>
      match Constr.Unsafe.kind body with
      | Constr.Unsafe.LetIn _ _ inner => Constr.Unsafe.substnl [v; g] 0 inner
      | _ => Constr.Unsafe.substnl [g] 0 body
      end
  | _ => fail_msg "onepass: lemma head is not a function of Γ"
  end.

(** First-order matching of [pat], open in the pattern variables
    [Rel 1 … Rel n], against the closed term [t], up to universe
    instances. [sub.(k-1)] receives the match of [Rel k]. *)
Ltac2 rec tmatch (n : int) (sub : constr option array) (pat : constr) (t : constr) : bool :=
  match Constr.Unsafe.kind pat with
  | Constr.Unsafe.Rel k =>
      if Int.le k n then
        match Array.get sub (Int.sub k 1) with
        | None => Array.set sub (Int.sub k 1) (Some t); true
        | Some u => Constr.equal u t
        end
      else false
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App g args' =>
          if Int.equal (Array.length args) (Array.length args')
          then if tmatch n sub f g then Array.for_all2 (tmatch n sub) args args' else false
          else false
      | _ => false
      end
  | Constr.Unsafe.Constant c _ =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.Constant c' _ => Constant.equal c c'
      | _ => false
      end
  | Constr.Unsafe.Ind i _ =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.Ind i' _ => Ind.equal i i'
      | _ => false
      end
  | Constr.Unsafe.Constructor c _ =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.Constructor c' _ => Constructor.equal c c'
      | _ => false
      end
  | Constr.Unsafe.Proj p _ c =>
      match Constr.Unsafe.kind t with
      (* folded and unfolded forms of a projection are the same operation *)
      | Constr.Unsafe.Proj p' _ c' =>
          if Ind.equal (Proj.ind p) (Proj.ind p') then
            if Int.equal (Proj.index p) (Proj.index p') then tmatch n sub c c' else false
          else false
      | _ => false
      end
  (* under binders only for closed comparisons, so de Bruijn indices need no shifting *)
  | Constr.Unsafe.Lambda b c =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.Lambda b' c' =>
          if Int.equal n 0 then
            if tmatch 0 sub (Constr.Binder.type b) (Constr.Binder.type b') then tmatch 0 sub c c' else false
          else Constr.equal pat t
      | _ => false
      end
  | Constr.Unsafe.Prod b c =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.Prod b' c' =>
          if Int.equal n 0 then
            if tmatch 0 sub (Constr.Binder.type b) (Constr.Binder.type b') then tmatch 0 sub c c' else false
          else Constr.equal pat t
      | _ => false
      end
  | _ => Constr.equal pat t
  end.

Ltac2 rec head_of (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => head_of f
  | _ => t
  end.

(** Atoms are identified up to conversion, as by the search-based quoter,
    but conversion is only tried between atoms whose heads agree up to
    universe instances. Conversion also records universe constraints. *)
Ltac2 same_atom (a : constr) (t : constr) : bool :=
  if Constr.equal a t then true
  else if tmatch 0 (Array.make 0 None) (head_of a) (head_of t) then Unification.conv_current a t
  else false.

(** An operation: its pattern body and arity, and its lemma head. *)
Ltac2 Type op := { pat : constr; arity : int; lemma : constr }.

Ltac2 rec strip_cast (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Cast c _ _ => strip_cast c
  | _ => t
  end.

(** a nullary pattern is usually written with an ascription, [(0 : Y)] *)
Ltac2 mk_op (p : constr) (l : constr) : op :=
  let n := lam_count p in { pat := strip_cast (lam_body n p); arity := n; lemma := l }.

(** the children of [t] if it is an instance of [o] *)
Ltac2 match_op (o : op) (t : constr) : constr list option :=
  let n := o.(arity) in
  let sub := Array.make n None in
  if tmatch n sub (o.(pat)) t then
    Some (List.map (fun i => Option.get (Array.get sub (Int.sub (Int.sub n i) 1))) (List.seq 0 1 n))
  else None.

Ltac2 Type rec qtree := [ QAtom (int, constr) | QOp (int, qtree list, constr) ].

Ltac2 rec find_atom (atoms : constr list) (t : constr) (i : int) : int option :=
  match atoms with
  | [] => None
  | a :: rest => if same_atom a t then Some i else find_atom rest t (Int.add i 1)
  end.

Ltac2 rec first_op (ops : op list) (i : int) (t : constr) : (int * constr list) option :=
  match ops with
  | [] => None
  | o :: rest =>
      match match_op o t with
      | Some cs => Some (i, cs)
      | None => first_op rest (Int.add i 1) t
      end
  end.

(** atoms are kept in discovery order *)
Ltac2 rec walk (ops : op list) (atoms : constr list) (t : constr) : qtree * constr list :=
  match first_op ops 0 t with
  | Some (i, cs) =>
      let rec go atoms cs :=
        match cs with
        | [] => ([], atoms)
        | c :: cs =>
            let (q, atoms) := walk ops atoms c in
            let (qs, atoms) := go atoms cs in
            (q :: qs, atoms)
        end in
      let (qs, atoms) := go atoms cs in
      (QOp i qs t, atoms)
  | None =>
      match find_atom atoms t 0 with
      | Some i => (QAtom i t, atoms)
      | None => (QAtom (List.length atoms) t, List.append atoms [t])
      end
  end.

Ltac2 rec mk_list (cons : constr) (nil : constr) (l : constr list) : constr :=
  match l with
  | [] => nil
  | a :: rest => mk_app cons [a; mk_list cons nil rest]
  end.

Ltac2 rec mk_nat (n : int) : constr :=
  if Int.equal n 0 then 'nno.nat_0 else mk_app 'nno.nat_S [mk_nat (Int.sub n 1)].

(** A lemma head instantiated at [Γ] and [ev]: a function of [k] arguments
    whose conclusion is [quote ev x y]; [xtmpl] is that [x], open in the
    arguments. With [beta], application substitutes into the body. *)
Ltac2 Type head := { hd : constr; nargs : int; xtmpl : constr; beta : bool }.

Ltac2 mk_head (h : constr) (k : int) (beta : bool) : head :=
  let t := prod_body k (Constr.type h) in
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App _ args =>
      if Int.equal (Array.length args) 5 then { hd := h; nargs := k; xtmpl := Array.get args 3; beta := beta }
      else fail_msg "onepass: lemma conclusion is not [quote f x y]"
  | _ => fail_msg "onepass: lemma conclusion is not [quote f x y]"
  end.

(** apply a head to [args] (in binder order): the proof and its free side *)
Ltac2 app_head (h : head) (args : constr list) : constr * constr :=
  let sub := List.rev args in
  let p := if h.(beta) then Constr.Unsafe.substnl sub 0 (lam_body (h.(nargs)) (h.(hd)))
           else mk_app (h.(hd)) args in
  (p, Constr.Unsafe.substnl sub 0 (h.(xtmpl))).

(** the proof of [quote ev x y], with [x] and [y] *)
Ltac2 rec build (heads : head list) (qvar : head) (t : qtree) : constr * constr * constr :=
  match t with
  | QAtom i y => let (p, x) := app_head qvar [mk_nat i; 'sprop.I] in (p, x, y)
  | QOp i qs y =>
      let rs := List.map (build heads qvar) qs in
      let xys := List.flat_map (fun (_, x, y) => [x; y]) rs in
      let ps := List.map (fun (p, _, _) => p) rs in
      let (p, x) := app_head (List.nth heads i) (List.append xys ps) in
      (p, x, y)
  end.

(** Reduce the goal [apos (l = r)] to [apos (x₁ = x₂)] in the free structure. *)
Ltac2 quote_equation (qev : constr) (qeq : constr) (qvar : constr) (cons : constr) (nil : constr)
    (ops : (constr * constr) list) : unit :=
  let ops' := List.map (fun (p, l) => mk_op p l) ops in
  lazy_match! goal with
  | [ |- apos (?l = ?r) ] =>
      let e := lazy_match! goal with [ |- apos ?e ] => e end in
      let (tl, atoms) := walk ops' [] l in
      let (tr, atoms) := walk ops' atoms r in
      let gid := Fresh.in_goal @Γ in
      Std.pose (Some gid) (mk_list cons nil atoms);
      let g := Control.hyp gid in
      let eid := Fresh.in_goal @ev in
      Std.pose (Some eid) (Constr.Unsafe.substnl [g] 0 (lam_body 1 qev));
      let v := Control.hyp eid in
      let heads := List.map (fun o =>
        let h := inst_env (o.(lemma)) g v in
        mk_head h (Int.mul 3 (o.(arity))) true) ops' in
      let qvar := mk_head (inst_env qvar g v) 2 false in
      let (p, x1, y1) := build heads qvar tl in
      let (q, x2, y2) := build heads qvar tr in
      let h := mk_app (inst_env qeq g v) [x1; y1; x2; y2; p; q] in
      (* the conclusion is the goal itself, not the type unification would
         infer through [ev]: otherwise the kernel may unfold the free
         structure's definition when checking against a cast goal *)
      refine open_constr:(@aimpl_impl_pos _ $e $h _);
      Control.plus (fun () => Std.clear [eid; gid]) (fun _ => ())
  | [ |- _ ] => fail_msg "onepass: goal is not an equation"
  end.

End onepass.

(** Ltac1 entry points, one per table size. [qev] is [fun Γ => eval Γ];
    [qeq] and [qvar] are [quote_equation] and [quote_var] at [ev], as lemma
    heads; [cons], [nil] build [Γ]; each [pᵢ], [lᵢ] is an operation. *)
Ltac quote_onepass_2 qev qeq qvar cons nil p1 l1 p2 l2 :=
  let f := ltac2:(qev qeq qvar cons nil p1 l1 p2 l2 |-
    let c x := Option.get (Ltac1.to_constr x) in
    onepass.quote_equation (c qev) (c qeq) (c qvar) (c cons) (c nil)
      [(c p1, c l1); (c p2, c l2)]) in
  f qev qeq qvar cons nil p1 l1 p2 l2.

Ltac quote_onepass_3 qev qeq qvar cons nil p1 l1 p2 l2 p3 l3 :=
  let f := ltac2:(qev qeq qvar cons nil p1 l1 p2 l2 p3 l3 |-
    let c x := Option.get (Ltac1.to_constr x) in
    onepass.quote_equation (c qev) (c qeq) (c qvar) (c cons) (c nil)
      [(c p1, c l1); (c p2, c l2); (c p3, c l3)]) in
  f qev qeq qvar cons nil p1 l1 p2 l2 p3 l3.
