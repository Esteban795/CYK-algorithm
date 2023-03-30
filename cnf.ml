(*
I'll call variables that do not have a derivation end-term.   

Example : 

X -> a, where a is an actual letter of the alphabet. 

a is an end-term. 
*)
type unit_rule = int * char
type binary_rule = int * int * int

type cnf = {
  initial :int;
  nb_variables : int;
  units : unit_rule list;
  binaries : binary_rule list;
  empty_word : bool
}

type tree = 
  |Unit of int * char 
  |Binary of int * tree * tree

type symbole = 
|T of char
|V of int

type regle = int * symbole list

type grammaire = {
  nb_variables : int;
  regles : regle list;
  initial : int;
}

(*Add initial rule, doesn't matter if it already exists or not*)
let start g = {
  nb_variables = g.nb_variables + 1;
  regles = (g.nb_variables,[V g.initial]) :: g.regles;
  initial = g.nb_variables
}
 
(*
Apply 'term' transformation. 
*)
let term g =
  let arr = Array.make 256 (-1) in
  let next_available = ref g.nb_variables in
  (*
  Map every single letter that are in the word onto new fresh variables   
  *)
  let rec get_fresh_variables mot =
    match mot with 
    | [] -> []
    | V i :: xs -> (V i) :: get_fresh_variables xs
    | T c :: xs ->
      let i = int_of_char c in
      if arr.(i) = -1 then begin
        arr.(i) <- !next_available;
        incr next_available 
      end;
      V arr.(i) :: get_fresh_variables xs
  in 

  (*
    For rules that look like this
    X -> something
    
    Create variables corresponding to end-terms and replace each occurence by
    the new variable

    Example : 
    X -> a
    
    becomes

    X -> N
    N -> a
  *)


  let transforme_regle (v, mot) = 
    if List.length mot <= 1 then (v,mot)
    else (v,get_fresh_variables mot)
  in 


  let regles_bis = ref (List.map transforme_regle g.regles) in 
  for i = 0 to 255 do 
    if arr.(i) <> -1 then 
      regles_bis := (arr.(i),[T (char_of_int i)]) :: !regles_bis
  done;

  {
    nb_variables = !next_available;
    regles = !regles_bis;
    initial = g.initial
  }


(*
On applique la transformation 'bin' du cours.
Dans binarise, on transforme toutes les règles de la forme
A -> X_1 ... X_k
par 
A -> X_1 A_1
A_i -> X_i+1 A_i+1
*)
let bin g = 
  let next_available = ref g.nb_variables in (*compter le nombre de variables totales*)

  (*
  On a X -> X_1 ... X_k
  et on renvoie 
  
  X -> X_1 Y_1 
  Y_1 -> X_2 Y_2
  Y_2 -> X_3 Y_3 
  .etc  (Y_i sont des variables qu'on a crée par nous-mêmes)
  *)
  let rec binarise (v,droite) = 
    match droite with 
    |[] | [ _ ] | [_ ; _] -> [(v,droite)] (*on a soit rien, soit une règle qui donne juste A -> X.. On l'éliminera à l'étape UNIT d'après*)
    | a :: b :: reste ->
      let nouvelle_variable = !next_available in 
      let nouvelle_regle = (v,[a ; V nouvelle_variable]) in 
      incr next_available;
      nouvelle_regle :: (binarise (nouvelle_variable,b :: reste))
  in 

  let rec traiter_regles l = 
    match l with 
    | [] -> []
    | r :: ls -> binarise r @ traiter_regles ls
  in 

  let regles' = traiter_regles g.regles in 
  {
    nb_variables = !next_available;
    regles = regles';
    initial = g.initial
  }

(*
On applique la transfo 'del' du cours. 
On commence par calculer les variables annulables
(Une variable est annulable si on a X -> epsilon ou X -> YZ avec Y et Z annulables)
*)
let del (g : grammaire) =

  (* On cherche les variables annulables *)
  let annulables = Array.make g.nb_variables false in
  let switch = ref true in 
  let traite_regle (v,droite) =
    let rec aux dr = 
      match dr with 
      | [] -> switch := true; annulables.(v) <- true; (* On arrive à Epsilon, donc c'est bien annulable *)
      | V x :: reste when annulables.(x) -> aux reste; (* On sait déjà qu'on a une variable annulable, donc il nous reste à vérifier le reste*)
      | _ -> () (* me les brise le linter avec le pattern matching pas exhaustif *)
    in 
    if not annulables.(v) then aux droite 
  in
  while !switch do 
    switch := false;
    List.iter traite_regle g.regles
  done;

  let rec traite_regles regles = 
    match regles with 
    | [] -> [] 
    | (v,[]) :: ls -> traite_regles ls (*on efface toutes les règles de la forme X -> epsilon*)
    | (v,[x]) :: ls -> (v,[x]) :: traite_regles ls (* On touche pas aux règles X -> a, où a est terminal*)
    | (v,[x ; y]) :: ls ->
      let temp = ref [] in 
      let ajouter_autre_si_annulable a b = 
        match a with 
        | V a' when annulables.(a') -> temp := (v,[b]) :: !temp
        | _ -> () (*pattern matching pas exhaustif*)
      in 
      ajouter_autre_si_annulable x y;
      ajouter_autre_si_annulable y x;
      !temp @ (v,[x ;y]) :: traite_regles ls
    | _ -> failwith "binarise abruti"
        
  in
  let regles_bis = 
    if annulables.(g.initial) then (g.initial,[]) :: traite_regles g.regles
    else traite_regles g.regles
  in 
  {
    nb_variables = g.nb_variables;
    regles = regles_bis;
    initial = g.initial
  }



(*
Transformation 'unit' du cours. 
On calcule la clôture unitaire de chaque variable, cad, pour chaque variable A,
les variables B tq A =>* B
Puis, pour chaque règle où B ∈ U(A)
-     B -> x, où x est terminal, on ajoute A -> x
-     B -> CD, on ajoute A -> CD
*)

(*
Pour créer la clôture unitaire, on transforme la grammaire en un graphe où les variables
sont les sommets, et il y a un arc entre X et Y ssi il y a une règle X -> Y
*)
let cree_graphe (g : grammaire) = 
  let n = g.nb_variables in 
  let graphe = Array.make n [] in 
  let traite_regle (v,droite) = 
    match droite with 
    |[V v'] -> 
      graphe.(v) <- v' :: graphe.(v)
    |_ -> ()
  in
  List.iter traite_regle g.regles;
  graphe


let cloture_transitive graphe = 
  let n = Array.length graphe in
  let cloture = Array.make_matrix n n false in 
  let calcule_ligne v = 
    let vus = Array.make n false in 
    let rec explore i = 
      if not vus.(i) then begin
        vus.(i) <- true;
        cloture.(v).(i) <- true;
        List.iter explore graphe.(v)
      end 
    in 
    explore v
  in for v = 0 to n - 1 do 
    calcule_ligne v
  done;
  cloture


let unit_fun g = 
  let cloture = cloture_transitive (cree_graphe g) in 
  let n = g.nb_variables in 
  let tab_regles = Array.make n [] in 

  (*
  On liste toutes les règles de la forme v -> ... dans un seul tableau de listes
  *)
  let ajouter_regles (v,droite) = 
    match droite with 
    |[ V _] -> ()
    | _ -> tab_regles.(v) <- droite :: tab_regles.(v)
  in 
  List.iter ajouter_regles g.regles;
  let regles_bis = ref [] in 
  for v = 0 to n - 1 do 
    for v' = 0 to n -  1 do
      if cloture.(v).(v') then begin 
        let f droite = regles_bis := (v,droite) :: !regles_bis in
        List.iter f tab_regles.(v')
      end
    done;
  done;
  {
    initial = g.initial;
    regles = !regles_bis;
    nb_variables = g.nb_variables
  } 

(*
On fait toutes les opérations dans le bon ordre, et on liste correctement les règles units et binaries   
*)
let normalise (g : grammaire) = 
  let g' = unit_fun (del ( bin ( term ( start g)))) in
  let units = ref [] in 
  let binaries = ref [] in 
  let empty_word = ref false in 
  let traite_regle (v,droite) = 
    match droite with 
    | [] -> assert (v = g'.initial); empty_word := true
    | [T c] -> units := (v,c) :: !units
    | [V x; V y] -> binaries := (v,x,y) :: !binaries
    | _ -> failwith "impossible"
  in 
  List.iter traite_regle g'.regles;

  {
    initial = g'.initial;
    nb_variables = g'.nb_variables;
    units = !units;
    binaries = !binaries;
    empty_word = !empty_word;
  }