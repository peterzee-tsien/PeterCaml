(* TODO: Q1a *)
let rec take (n : int) (s : 'a stream) : 'a list =
  match n with
  | 0 -> []
  | 1 -> [s.head]
  | _ -> s.head :: take (n-1) (s.tail ())
(* TODO: Q1b *)
let rec drop (n : int) (s : 'a stream) : 'a stream =
  match n with
  | 0 -> s
  | _ -> drop (n-1) (s.tail ())

(* TODO: Q2a *)
let zeroes : int stream =
  { head = 0;
    tail=  (fun () -> (unfold (fun x -> (x,x) ) 0))}

(* TODO: Q2b *)
let natural_numbers : int stream = 
  { head = 0; 
    tail = (fun () -> (unfold (fun x -> (x,x+1)) 1) )}
  

(* TODO: Q2c *)
let even_numbers : int stream =
  {head = 0;
   tail = (fun () -> (unfold (fun x -> (x,x+2)) 2))
  }

(* TODO: Q3 *)
let rec map2 (f : 'a -> 'b -> 'c) (s1 : 'a stream) (s2 : 'b stream) : 'c stream =
  { head = (f s1.head s2.head);
    tail = (fun () -> (map2 f (drop 1 s1) (drop 1 s2) ))
  }

(* TODO: Q4a *)
let fibonacci : int stream =
  {
    head = 0;
    tail = (fun () -> (unfold (fun (x,y) -> (x,(y,x+y))) (1,1)))
  }

(* TODO: Q4b *)
let lucas : int stream =
  {
    head = 2;
    tail = (fun () -> (unfold (fun (x,y) -> (x,(y,x+y))) (1,3)))
  }

