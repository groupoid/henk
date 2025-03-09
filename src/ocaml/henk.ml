(* Henk: CoC 1988 with infinite hierarchy of predicative universes *)

type term =
    | Var of string
    | Universe of int
    | Pi of string * term * term   (* ∀ (x : a), b *)
    | Lam of string * term * term  (* λ (x : a), b *)
    | App of term * term

let rec string_of_term = function
    | Var x -> x
    | Universe u -> "U_" ^ string_of_int u
    | Pi (x, a, b) -> "∀ (" ^ x ^ " : " ^ string_of_term a ^ "), " ^ string_of_term b
    | Lam (x, a, t) -> "λ (" ^ x ^ " : " ^ string_of_term a ^ "), " ^ string_of_term t
    | App (t1, t2) -> "(" ^ string_of_term t1 ^ " " ^ string_of_term t2 ^ ")"

type context = (string * term) list
exception TypeError of string

let universe = function
    | Universe i -> i
    | ty -> raise (TypeError ("Expected a universe"))

let rec subst x s = function
    | Var y -> if x = y then s else Var y
    | Pi (y, a, b) when x <> y -> Pi (y, subst x s a, subst x s b)
    | Lam (y, a, b) when x <> y -> Lam (y, subst x s a, subst x s b)
    | App (f, a) -> App (subst x s f, subst x s a)
    | t -> t

let rec lookup x = function
    | [] -> raise (TypeError ("Unbound variable: " ^ x))
    | (y, typ) :: rest -> if x = y then typ else lookup x rest

let rec equal ctx t1 t2 = match t1, t2 with
    | Var x, Var y -> x = y
    | Universe i, Universe j -> i <= j
    | Pi (x, a, b), Pi (y, a', b')
    | Lam (x, a, b), Lam (y, a', b') -> equal ctx a a' && equal ((x,a) :: ctx) b (subst y (Var x) b')
    | Lam (x, _, b), t -> equal ctx b (App (t, Var x))
    | t, Lam (x, _, b) -> equal ctx (App (t, Var x)) b
    | App (f, a), App (f', a') -> equal ctx f f' && equal ctx a a'
    | _ -> false

and reduce ctx t = match t with
    | App (Lam (x, _, b), a) -> subst x a b
    | App (Pi (x, _, b), a) -> subst x a b
    | App (f, a) -> App (reduce ctx f, reduce ctx a)
    | _ -> t

and normalize ctx t =
    let t' = reduce ctx t in
    if equal ctx t t' then t else normalize ctx t'

and infer ctx t = let res = match t with
    | Var x -> lookup x ctx
    | Universe i -> Universe (i + 1)
    | Pi (x, a, b) -> Universe (max (universe (infer ctx a)) (universe (infer ((x,a)::ctx) b)))
    | Lam (x, a, b) -> let _ = infer ctx a in Pi (x, a, infer ((x,a)::ctx) b)
    | App (f, a) -> match infer ctx f with | Pi (x, a, b) -> subst x a b | t -> raise (TypeError "Requires a Pi type.")
    in normalize ctx res

(* Test Suite *)

let nat_type =
    Pi ("Nat", Universe 0,
    Pi ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Pi ("Zero", Var "Nat", Var "Nat")))

let zero =
    Lam ("Nat", Universe 0,
    Lam ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lam ("Zero", Var "Nat", Var "Zero")))

let succ =
    Lam ("pred", nat_type,
    Lam ("Nat", Universe 0,
    Lam ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lam ("Zero", Var "Nat",
    App (Var "Succ", App (App (App (Var "pred", Var "Nat"), Var "Succ"), Var "Zero"))))))

let list_type =
    Pi ("List", Universe 0,
    Pi ("Cons", Pi ("head", nat_type, Pi ("tail", Var "List", Var "List")),
    Pi ("Nil", Var "List", Var "List")))

let sum =
    Lam ("xs", list_type,
    App (App (App (Var "xs", nat_type),
    Lam ("head", nat_type,
    Lam ("tail", nat_type,
    Lam ("Nat", Universe 0,
    Lam ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lam ("Zero", Var "Nat",
    App (App (App (Var "head", Var "Nat"), App (App (Var "tail", Var "Nat"), Var "Succ")),
    Var "Zero"))))))), zero))

let one =
    Lam ("Nat", Universe 0,
    Lam ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lam ("Zero", Var "Nat",
    App (Var "Succ", Var "Zero"))))

let two =
    Lam ("Nat", Universe 0,
    Lam ("Succ", Pi ("n", Var "Nat", Var "Nat"),
    Lam ("Zero", Var "Nat",
    App (Var "Succ",
    App (Var "Succ", Var "Zero")))))

let nil =
    Lam ("List", Universe 1,
    Lam ("Cons", Pi ("head", nat_type, Pi ("tail", Var "List", Var "List")),
    Lam ("Nil", Var "List",
    Var "Nil")))

let cons head tail =
    Lam ("List", Universe 1,
    Lam ("Cons", Pi ("head", nat_type, Pi ("tail", Var "List", Var "List")),
    Lam ("Nil", Var "List", App (App (Var "Cons", head), tail))))

let list_one_two = cons one (cons two nil)

let rec test_equal ctx t1 t2 =
    let t1' = normalize ctx t1 in
    let t2' = normalize ctx t2 in
    equal ctx t1' t2'

let run_type_test name term expected_type =
    let ctx = [] in
    try let inferred = infer ctx term in
        let norm_inferred = normalize ctx inferred in
        let norm_expected = normalize ctx expected_type in
        Printf.printf "Test %s:\n- Term: %s\n- Inferred: %s\n- Expected: %s\n- Result: %s\n\n"
          name
          (string_of_term term)
          (string_of_term norm_inferred)
          (string_of_term norm_expected)
          (if test_equal [] norm_inferred norm_expected then "PASS" else "FAIL")
    with | Failure msg -> Printf.printf "Universe Test %s: Failed with error: %s\n\n" name msg

let run_equality_test ctx name (t1, t2) =
    let result = test_equal ctx t1 t2 in
    Printf.printf "Equality Test %s:\n- Term1: %s\n- Term2: %s\n- Result: %s\n\n"
      name
      (string_of_term t1)
      (string_of_term t2)
      (if result then "PASS" else "FAIL")


let beta           = (App (Lam ("x", Universe 0, Var "x"), Var "y"), Var "y")
let eta            = (Lam ("x", Universe 0, App (Var "f", Var "x")), Var "f")
let eta_domain     = (Lam ("x", Universe 1, App (Var "f", Var "x")), Var "f")
let invalid_eta    = (Lam ("x", Universe 0, Universe 0), Universe 0)
let invalid_eta_v  = (Lam ("x", Universe 0, Var "u"), Var "u")
let eta_subtle     = (Lam ("x", Universe 0, Var "u"), Var "u")
let tricky_eta     = (Lam ("x", Universe 0, App (Var "f", Var "u")), Var "u")
let invalid_tricky = (Lam ("x", Universe 0, App (Var "id", Var "u")), Var "u")
let multi_beta     = (App (App (Lam ("x", Universe 0, Lam ("y", Universe 0, Var "x")), Var "u"), Var "y"), Var "u")
let predicative    = Pi ("x", Universe 0, Universe 0)
let neutral_eta    = (Lam ("x", Universe 0, App (Var "f", Var "u")), App (Var "f", Var "u"))

let () =
    let ctx = [("s", succ);("f", Pi ("x", Universe 0, Universe 0)); ("u", Universe 0); ("y", Universe 0); ("id", Pi ("x", Universe 0, Var "x"))] in
    run_type_test "Nat" nat_type (Universe 1);
    run_type_test "Zero" zero nat_type;
    run_type_test "Succ" succ (Pi ("pred", nat_type, nat_type));
    run_type_test "Sum" sum (Pi ("xs", list_type, nat_type));
    run_equality_test ctx "Beta" beta;
    run_equality_test ctx "Eta" eta;
    run_equality_test ctx "Invalid Eta" invalid_eta;
    run_equality_test ctx "Invalid Eta Var" invalid_eta_v;
    run_equality_test ctx "Tricky Eta" tricky_eta;
    run_equality_test ctx "Invalid Tricky Eta" invalid_tricky;
    run_equality_test ctx "Multi Beta" multi_beta;
    run_equality_test ctx "Eta Domain" eta_domain;
    run_type_test "CoC with Predicative Hierarchy" predicative (Universe 1);
    run_equality_test ctx "Neutral Eta" neutral_eta;
