(*--------------------------------------------------------------*)
(* Q1 : String to Characters to String                  *)
(*--------------------------------------------------------------*)

(* 1.1 Turn a string into a list of characters. *)
let string_explode (s : string) : char list =
  tabulate (fun f-> (String.get s f)) (String.length s)

(* 1.2 Turn a list of characters into a string. *)
let string_implode (l : char list) : string =
  List.fold_left (fun a b -> a ^ String.make 1 b) "" l

(* ------------------------------------------------------------------------*)
(* Q2 : Bank Account *)
(* ------------------------------------------------------------------------*)

let open_account (pass: password) : bank_account =
  let pw = ref pass in 
  let deposit = ref 0 in 
  {update_pass = (fun old n -> if not (String.equal (!pw) old) then raise wrong_pass else pw:=n) ; 
   retrieve = (fun p i-> if not (String.equal !pw p) then raise wrong_pass
                else if 
                  i<0 then raise negative_amount
                else if  
                  !deposit<i then raise not_enough_balance 
                else
                  deposit:= !deposit - i);
   deposit = (fun p i-> if not (String.equal !pw p) then raise wrong_pass
               else if 
                 i<0 then raise negative_amount 
               else 
                 deposit:= !deposit + i);
   show_balance=(fun p ->if not (String.equal !pw p) then raise wrong_pass else
                    !deposit) }
;;

