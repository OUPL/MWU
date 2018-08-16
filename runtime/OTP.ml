(** Type definitions and string conversions **)
type d = { num : Big.big_int; den : Big.big_int }

let num_strats = 17
let num_rounds = 24
                   
let enumStrats =
  let rec incRec l n target =
    if (n > target)
    then incRec ((Big.of_int (n-1))::l) (n - 1) target
    else l
  in incRec [] num_strats 0

let rec stringOfbig_list l =
  match l with
  | [] -> ""
  | a::l' -> (Big.to_string a) ^ (stringOfbig_list l')
                    
let testList =
  List.map (fun x -> {num = x; den = x}) enumStrats

(* This is a zero cost vector *)           
let testList2 =
  List.map (fun x -> (x, {num = Big.zero; den = x})) enumStrats
           
let stringOfd x =
  ((Big.to_string x.num)^"#"^(Big.to_string x.den))

let dOfString s =
  let dvalues =
    List.map Big.of_string (Str.split (Str.regexp "#") s) in
  {num = List.hd (dvalues); den = List.hd (List.tl (dvalues))}

let stringOfbigd_pair x =
(* We can assume an implicit ordering
    of the strats *)
  (stringOfd (snd x)) ^ " "
    
let rec stringOfdlist l =
  match l with
  | [] -> ""
  | a::l' -> (stringOfd a)^" "^(stringOfdlist l')
                                 
let rec stringOfbigd_pair_list l =
  match l with
  | [] -> ""
  | a::l' -> (stringOfbigd_pair a) ^ (stringOfbigd_pair_list l')
                                 
let dlistOfstring s =
  List.map dOfString (Str.split (Str.regexp " ") s)

           
(** Networking components **)           
let inBuff_client : in_channel = open_in "./clientOutput"
let outBuff_client : out_channel = open_out "./clientInput"

let outBuff_env : out_channel = open_out "./envInput"
let inBuff_env : in_channel = open_in "./envOutput"

let rec recvMessage (n : int) : unit =
  if n <= 0
  then ()
  else (
    (* receive weights vector from client *)
    print_string "receiving a message from client";
    print_newline();
    
    (* Send a string representation of weights vector to environment *)
    output_string
      outBuff_env
      ((stringOfbigd_pair_list
         (Marshal.from_channel inBuff_client)) ^ "\n");
    flush outBuff_env;
    print_string "Sent message to environment";
    print_newline();

    (* If this fails, make sure the list
       sent by the environment has the correct length *)
    Marshal.to_channel
      outBuff_client
      (List.combine
         (enumStrats)
         (dlistOfstring (input_line inBuff_env)))
      [];
    flush outBuff_client;
   
    print_string "Sent message to client";
    print_newline();
   
    recvMessage (n-1))

let () =
        recvMessage num_rounds
