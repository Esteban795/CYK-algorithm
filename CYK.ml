(*
COCKE-YOUNGER-KASAMI algorithm
Pseudo-code : 
---------------------------------------------------------------------------------------------------------------
function CYK(g,w)
  if w = empty_word : renvoyer S -> empty_word
  n = word's length
  k = number of variables
  t = 3D-matrix of (n + 1) * n * k, all initialized to false

  for each rule Xi -> a do
    for d = 0 to n - 1 do
      if w[d] = a then t[1,d,i] <- true 

  for l = 2 to n do 
    for d = 0 to n - l do
     for l' = 0 to l - 1 do 
      for each rule X_i -> X_jX_k do 
        t[l,d,i] <- t[l,d,i] || ( t[l',d,i] && t[l - l', d + l',i])
  
  return t[n,0,g.initial]
--------------------------------------------------------------------------------------------------------------
*)

open Cnf

(*An example*)
let g0 = {
 initial = 0;
 nb_variables = 5;
 units = [(0,'b');(1,'a');(2, 'b');(4,'a')];
 binaries = [(0,1,2); (0,2,1); (0,3,1); (1,1,4); (3,1,2)];
 empty_word = false
}

let cyk_recognize (g : cnf) (s : string) = 
  if s = "" then g.empty_word (* don't waste time *)
  else
  let n = String.length s in
  let k = g.nb_variables in 
  let t = Array.make_matrix (n + 1) n [||] in 

  for i = 0 to n do 
    for j = 0 to n - 1 do 
      t.(i).(j) <- Array.make k false
    done;
  done;

  
  for d = 0 to n - 1 do
    List.iter (fun (i, c) -> if c = s.[d] then t.(1).(d).(i) <- true) g.units
  done;

  for l = 2 to n do 
    for d = 0 to n - 1 do
      for l' = 0 to l - 1 do
        if d + l' < n then List.iter (fun (a,b,c) -> t.(l).(d).(a) <- t.(l).(d).(a) || (t.(l').(d).(b) && t.(l - l').(d + l').(c))) g.binaries
      done;
    done;
  done;
  t.(n).(0).(g.initial)


exception No_tree
let cyk_analyze (g : cnf) (s : string) = 
  if s = "" then raise No_tree (* else it breaks the code *)
  else
  let n = String.length s in
  let k = g.nb_variables in 
  let t = Array.make_matrix (n + 1) n [||] in 

  for i = 0 to n do 
    for j = 0 to n - 1 do 
      t.(i).(j) <- Array.make k None;
    done;
  done;

  
  for d = 0 to n - 1 do
    List.iter (fun (i, c) -> if c = s.[d] then t.(1).(d).(i) <- Some (Unit (i,c))) g.units
  done;

  for l = 2 to n do 
    for d = 0 to n - l do
      for l' = 0 to l - 1 do
        let traiter (a,b,c) = 
          match t.(l).(d).(a), t.(l').(d).(b), t.(l - l').(d + l').(c) with
          | None , Some i, Some j ->
              t.(l).(d).(a) <- Some (Binary (a,i,j))
          | _ -> ()
        in 
        List.iter traiter g.binaries
      done;
    done;
  done;
  
  match t.(n).(0).(g.initial) with 
  | None -> raise No_tree
  | Some x -> x


let cyk_count (g : cnf) (s : string) = 
  let n = String.length s in
  let k = g.nb_variables in 
  let t = Array.make_matrix (n + 1) n [||] in 

  for i = 0 to n do 
    for j = 0 to n - 1 do 
      t.(i).(j) <- Array.make k 0;
    done;
  done;

  let traiter_unitaire (i,c) = 
    for j = 0 to n - 1 do 
      if s.[j] = c then t.(1).(j).(i) <- 1
    done;
  in
  List.iter traiter_unitaire g.units;

  for l = 2 to n do 
    for d = 0 to n - l do
      for l' = 0 to l - 1 do
        let traiter_binaire (i,j,k) = 
          t.(l).(d).(i) <- t.(l).(d).(i) + (t.(l').(d).(j) * t.(l - l').(d + l').(k))
        in
        List.iter traiter_binaire g.binaries
      done;
    done;
  done;
  if n = 0 && g.empty_word then 1
  else  if n = 0 then 0 
  else t.(n).(0).(g.initial)