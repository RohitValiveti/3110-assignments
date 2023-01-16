(************************************************************
   Copyright (C) 2022 Cornell University.
   Created by Michael Clarkson (mrc26@cornell.edu) and CS 3110 course staff.
   You may not redistribute this assignment, distribute any derivatives,
   or use it for commercial purposes.
 ************************************************************)

(** CS 3110 Spring 2022 Assignment A1 Enigma

    @author Rohit Valiveti (rvv6) *)

(************************************************************

  Academic Integrity Statement

  I, the person named in the author comment above, have fully reviewed
  the course academic integrity policies. I have adhered to those
  policies in solving the assignment.

  The policies do permit some limited collaboration among students
  currently enrolled in the course. If I did engage in such
  collaboration, here is the list of other students with whom I
  collaborated, and a brief summary of that collaboration:

  - none

  ************************************************************)

(** [index c] is the 0-based index of [c] in the alphabet. Requires: [c]
    is an uppercase letter in A..Z. *)
let index (c : char) : int = Char.code c - 65

(**[wrap_25 input_pos letter] is the 0 based index of [letter] +
   [input_pos] in the alphabet. [wrap_25 input_pos letter] accounts for
   an index > 25 by wrapping around to 0. Requires: [letter] is in A..Z*)
let wrap_25 (input_pos : int) (letter : char) : int =
  if input_pos + index letter > 25 then input_pos + index letter - 26
  else input_pos + index letter

(**[wrap_0 input_pos letter] is the 0 based index of [letter] -
   [input_pos] in the alphabet. [wrap_0 input_pos letter] accounts for
   an index < 0 by wrapping around to 25. Requires: [letter] is in A..Z*)
let wrap_0 (letter : char) (input_pos : int) : int =
  if input_pos - index letter < 0 then 26 + input_pos - index letter
  else input_pos - index letter

(** [map_r_to_l wiring top_letter input_pos] is the left-hand output
    position at which current would appear when current enters at
    right-hand input position [input_pos] to a rotor whose wiring
    specification is given by [wiring]. The orientation of the rotor is
    given by [top_letter], which is the top letter appearing to the
    operator in the rotor's present orientation. Requires: [wiring] is a
    valid wiring specification, [top_letter] is in A..Z, and [input_pos]
    is in 0..25. *)
let map_r_to_l (wiring : string) (top_letter : char) (input_pos : int) :
    int =
  top_letter |> wrap_25 input_pos |> String.get wiring |> index
  |> wrap_0 top_letter

(**[inverse_index num] is the character in the alphabet associated with
   the 0-based index [num]. Requires: [num] is in 0..25 *)
let inverse_index (num : int) : char = Char.chr (num + 65)

(** [map_l_to_r] computes the same function as [map_r_to_l], except for
    current flowing left to right. *)
let map_l_to_r (wiring : string) (top_letter : char) (input_pos : int) :
    int =
  top_letter |> wrap_25 input_pos |> inverse_index
  |> String.index wiring |> wrap_0 top_letter

(** [map_refl wiring input_pos] is the output position at which current
    would appear when current enters at input position [input_pos] to a
    reflector whose wiring specification is given by [wiring]. Requires:
    [wiring] is a valid reflector specification, and [input_pos] is in
    0..25. *)
let map_refl (wiring : string) (input_pos : int) : int =
  map_r_to_l wiring 'A' input_pos

(** [map_plug plugs c] is the letter to which [c] is transformed by the
    plugboard [plugs]. Requires: [plugs] is a valid plugboard, and [c]
    is in A..Z. *)
let rec map_plug (plugs : (char * char) list) (c : char) =
  match plugs with
  | [] -> c
  | (c1, c2) :: lst ->
      if c = c1 then c2 else if c = c2 then c1 else map_plug lst c

type rotor = {
  wiring : string;  (** A valid rotor wiring specification. *)
  turnover : char;
      (** The turnover of the rotor, which must be an uppercase letter.
          This field will not be used in the assignment until you
          implement stepping in the excellent scope. *)
}
(** [rotor] represents an Enigma rotor. *)

type oriented_rotor = {
  rotor : rotor;  (** The rotor. *)
  top_letter : char;  (** The top letter showing on the rotor. *)
}
(** [oriented_rotor] represents a rotor that is installed on the spindle
    hence has a top letter. *)

type config = {
  refl : string;  (** A valid reflector wiring specification. *)
  rotors : oriented_rotor list;
      (** The rotors as they are installed on the spindle from left to
          right. There may be any number of elements in this list: 0, 1,
          2, 3, 4, 5, etc. The order of elements in list represents the
          order in which the rotors are installed on the spindle, **from
          left to right**. So, the head of the list is the leftmost
          rotor on the spindle, and the last element of the list is the
          rightmost rotor on the spindle. *)
  plugboard : (char * char) list;
      (** A valid plugboard. The order of characters in the pairs does
          not matter, and the order of pairs in the list does not
          matter. *)
}
(** [config] represents the configuration of an Enigma machine. *)

(** [map_rotors_r_to_l rotors input_pos] is the index of the character
    typed after the current travels through the rotors from right to
    left. Requires: [rotors] is a valid oriented_rotor list and
    [input_pos] is in 0..25]*)
let rec map_rotors_r_to_l
    (rotors : oriented_rotor list)
    (input_pos : int) : int =
  match rotors with
  | [] -> input_pos
  | h :: k ->
      map_r_to_l h.rotor.wiring h.top_letter
        (map_rotors_r_to_l k input_pos)

(** [map_rotors_l_to_r rotors input_pos] is the index of the character
    typed after the current travels through the rotors from left to
    right. Requires: [input_pos] is in 0..25]*)
let rec map_rotors_l_to_r
    (rotors : oriented_rotor list)
    (input_pos : int) : int =
  match rotors with
  | [] -> input_pos
  | h :: k ->
      map_rotors_l_to_r k
        (map_l_to_r h.rotor.wiring h.top_letter input_pos)

(** [cipher_char config c] is the letter to which the Enigma machine
    ciphers input [c] when it is in configuration [config]. Requires:
    [config] is a valid configuration, and [c] is in A..Z. *)
let cipher_char (config : config) (c : char) : char =
  c
  |> map_plug config.plugboard
  |> index
  |> map_rotors_r_to_l config.rotors
  |> map_refl config.refl
  |> map_rotors_l_to_r config.rotors
  |> inverse_index
  |> map_plug config.plugboard

(**[incr_wrap num] adds 1 to [num] and evaluates to 0 if it is > 25.
   Requires: [num] is in 1..25 *)
let incr_wrap (num : int) : int = if num + 1 > 25 then 0 else num + 1

(** [step_neighbor o_list] increments the top_letter of the of first
    oriented_rotor in list [o_list] *)
let step_neighbor (o_list : oriented_rotor list) : oriented_rotor list =
  match o_list with
  | [] -> [] (* Will never run *)
  | [ h ] ->
      [
        {
          rotor = h.rotor;
          top_letter =
            h.top_letter |> index |> incr_wrap |> inverse_index;
        };
      ]
  | h :: k ->
      [
        {
          rotor = h.rotor;
          top_letter =
            h.top_letter |> index |> incr_wrap |> inverse_index;
        };
      ]
      @ k

(** [check_neighbor o_list] increments the top_letter of the first
    oriented_rotor of [o_list] only if that rotor is at its turnover and
    it has a neighboring oriented_rotor *)
let rec check_neighbor (o_list : oriented_rotor list) :
    oriented_rotor list =
  match o_list with
  | [] -> []
  | [ h ] -> [ h ]
  | h :: k ->
      if h.top_letter |> index = (h.rotor.turnover |> index) then
        [
          {
            rotor = h.rotor;
            top_letter =
              h.top_letter |> index |> incr_wrap |> inverse_index;
          };
        ]
        @ step_neighbor k
      else [ h ] @ check_neighbor k

let step_rotor (o_list : oriented_rotor list) : oriented_rotor list =
  o_list

(** [step config] is the new configuration to which the Enigma machine
    transitions when it steps beginning in configuration [config].
    Requires: [config] is a valid configuration. *)
let rec step (config : config) : config =
  match config.rotors with
  | [] -> config
  | [ h ] ->
      {
        refl = config.refl;
        rotors =
          [
            {
              rotor = h.rotor;
              top_letter =
                h.top_letter |> index |> incr_wrap |> inverse_index;
            };
          ];
        plugboard = config.plugboard;
      }
  | h :: k ->
      {
        refl = config.refl;
        rotors =
          (* Increment the top_letter of h and rotor to its left if h is
             at its turnover *)
          (if h.top_letter |> index = (h.rotor.turnover |> index) then
           [
             {
               rotor = h.rotor;
               top_letter =
                 h.top_letter |> index |> incr_wrap |> inverse_index;
             };
           ]
           @ step_neighbor k
           (* Check if any other rotors are at their turnover and
              increment their top_letter accordingly *)
          else
            [
              {
                rotor = h.rotor;
                top_letter =
                  h.top_letter |> index |> incr_wrap |> inverse_index;
              };
            ]
            @ check_neighbor k);
        plugboard = config.plugboard;
      }

(**[string_to_char_list s] is the list of chars representing each letter
   in [s] Refered to: https://github.com/ocaml/ocaml/issues/5367*)
let string_to_char_list s =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

(**[combine_chars chars] produces a string by combining each char
   element of [chars]. Requires: each char in [chars] is in A..Z*)
let rec char_list_to_string (chars : char list) : string =
  match chars with
  | [] -> ""
  | h :: k -> Char.escaped h ^ char_list_to_string k

(** [cipher config s] is the string to which [s] enciphers when the
    Enigma machine begins in configuration [config]. Requires: [config]
    is a valid configuration, and [s] contains only uppercase letters. *)
let rec cipher (config : config) (s : string) : string =
  match string_to_char_list s with
  | [] -> ""
  | h :: k ->
      (h |> cipher_char (step config) |> Char.escaped)
      ^ cipher (step config) (char_list_to_string k)

let hours_worked = 10
