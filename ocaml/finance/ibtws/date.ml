
type datetime = {
  year: int;
  mounth: int;
  day: int;
  hour: int;
  minute: int;
  second: int;
  tz: string;
};;

let int2string (i: int) (size: int) : string =
  let s = string_of_int i in
  if String.length s > size then
    raise (Failure "int2string: string rep. to long")
  else
    if String.length s < size then (
      let prefix = String.make (size - String.length s) '0' in
      String.concat "" [prefix; s]
    ) else s
;;

open Spotlib.Spot
open Planck;;

(* Stream of chars with buffering and memoization *)
module Stream = struct

  (* The configuration of the stream *)    
  module Base = struct

    (* Stream elements *)
    type elem = char (* It is a char stream *)
    let show_elem = Printf.sprintf "%C" (* How to pretty print the element *)
    let equal_elem (x : char) y = x = y

    (* Stream attributes *)
    type attr = Sbuffer.buf (* Stream elements carry internal buffers *)
    let default_attr = Sbuffer.default_buf

    (* Stream positions *)
    module Pos = Position.File (* Type of the element position *)
    let position_of_attr attr = Sbuffer.position_of_buf attr (* How to obtain the position from attr *)
  end

  module Str = Stream.Make(Base) (* Build the stream *)
  include Str

  (* Extend Str with buffering *)
  include Sbuffer.Extend(struct
    include Str
    let create_attr buf = buf (* How to create an attribute from a buffer *)
    let buf st = attr st (* How to obtain the buffer of a stream *)
  end)

end

module Parser = struct

  module Base = Pbase.Make(Stream) (* Base parser *)
  include Base

  include Pbuffer.Extend(Stream)(Base) (* Extend Base with parser operators for buffered streams *)
end    

open Parser (* open Parser namespace *)

(*
  parser for format
  
  yyyymmdd{space}{space}hh:mm:dd
*)

let num_parser: string Parser.t =
  one_of ['0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9'] >>= fun c -> return (String.make 1 c)
;;

let rec datetime_parser: datetime Parser.t =
  num_parser >>= fun y0 ->
  num_parser >>= fun y1 ->
  num_parser >>= fun y2 ->
  num_parser >>= fun y3 ->
  num_parser >>= fun mo0 ->
  num_parser >>= fun mo1 ->
  num_parser >>= fun d0 ->
  num_parser >>= fun d1 ->
  token ' ' >>= fun () ->
  token ' ' >>= fun () ->
  num_parser >>= fun h0 ->
  num_parser >>= fun h1 ->
  token ':' >>= fun () ->
  num_parser >>= fun mi0 ->
  num_parser >>= fun mi1 ->
  token ':' >>= fun () ->
  num_parser >>= fun s0 ->
  num_parser >>= fun s1 ->

  return {
    year = int_of_string (String.concat "" [y0; y1; y2; y3]);
    mounth = int_of_string (String.concat "" [mo0; mo1]);
    day = int_of_string (String.concat "" [d0; d1]);
    hour = int_of_string (String.concat "" [h0; h1]);
    minute = int_of_string (String.concat "" [mi0; mi1]);
    second = int_of_string (String.concat "" [s0; s1]);
    tz = "";
  }
and parse_datetime (s: string) : datetime =
  let stream = Stream.from_string ~filename:"stdin" s in
  match datetime_parser stream with
  | Result.Ok (res, _) -> 
    res
  | Result.Error (pos, s) ->
    Format.eprintf "%a: syntax error: %s@." Position.File.format pos s;      
    raise Pervasives.Exit
;;


(*
  transform a datetime into the following format 
  yyyymmdd HH:mm:ss ttt

  (ttt being optional)
*)  
let datetime_to_string (dt: datetime) : string =
  let year = int2string dt.year 4 in
  let mounth = int2string dt.mounth 2 in
  let day = int2string dt.day 2 in

  let date = String.concat "" [year; mounth; day] in

  let hour = int2string dt.hour 2 in
  let min = int2string dt.minute 2 in
  let sec = int2string dt.second 2 in

  let time = String.concat ":" [hour; min; sec] in

  let tz = if dt.tz = "" then [] else [dt.tz] in

  String.concat " " ([date; time] @ tz)
;;
  
type duration = Second of int
		| Day of int
		| Week of int
;;

let duration2string (d: duration) : string =
  match d with
    | Second i -> String.concat " " [string_of_int i; "S"]
    | Day i -> String.concat " " [string_of_int i; "D"]
    | Week i -> String.concat " " [string_of_int i; "W"]
;;

type barSize = SEC1
	       | SEC5
	       | SEC15
	       | SEC30
	       | MIN1
	       | MIN2
	       | MIN3
	       | MIN5
	       | MIN15
	       | MIN30
	       | HOUR1
	       | DAY1
;;

let barSize2string (bs: barSize) : string =
  match bs with
    | SEC1 -> "1 sec"
    | SEC5 -> "5 sec"
    | SEC15 -> "15 sec"
    | SEC30 -> "30 sec"
    | MIN1 -> "1 min"
    | MIN2 -> "2 mins"
    | MIN3 -> "3 mins"
    | MIN5 -> "5 mins"
    | MIN15 -> "15 mins"
    | MIN30 -> "30 mins"
    | HOUR1 -> "1 hour"
    | DAY1 -> "1 day"
;;
      
let diff_datetime (d1: datetime) (d2: datetime): datetime =
  raise (Failure "NYI");;

let now (): datetime =
  raise (Failure "NYI");;
