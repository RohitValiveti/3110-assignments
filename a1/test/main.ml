open OUnit2
open Enigma

(** [index_test name input expected_output] constructs an OUnit test
    named [name] that asserts the quality of [expected_output] with
    [index input]. *)
let index_test (name : string) (input : char) (expected_output : int) :
    test =
  name >:: fun _ ->
  (* the [printer] tells OUnit how to convert the output to a string *)
  assert_equal expected_output (index input) ~printer:string_of_int

(** [] *)
let map_rl_test
    (name : string)
    (input_wiring : string)
    (input_top_letter : char)
    (input_input_pos : int)
    (expected_output : int) : test =
  name >:: fun _ ->
  assert_equal expected_output
    (map_r_to_l input_wiring input_top_letter input_input_pos)
    ~printer:string_of_int

(** [] *)
let map_lr_test
    (name : string)
    (input_wiring : string)
    (input_top_letter : char)
    (input_input_pos : int)
    (expected_output : int) : test =
  name >:: fun _ ->
  assert_equal expected_output
    (map_l_to_r input_wiring input_top_letter input_input_pos)
    ~printer:string_of_int

(** [] *)
let map_refl_test
    (name : string)
    (input_wiring : string)
    (input_input_pos : int)
    (expected_output : int) : test =
  name >:: fun _ ->
  assert_equal expected_output
    (map_refl input_wiring input_input_pos)
    ~printer:string_of_int

(** [] *)
let map_plug_test
    (name : string)
    (input_plugs : (char * char) list)
    (input_c : char)
    (expected_output : char) : test =
  name >:: fun _ ->
  assert_equal expected_output
    (map_plug input_plugs input_c)
    ~printer:Char.escaped

(** [] *)
let cipher_char_test
    (name : string)
    (input_config : config)
    (input_c : char)
    (expected_output : char) : test =
  name >:: fun _ ->
  assert_equal expected_output
    (cipher_char input_config input_c)
    ~printer:Char.escaped

(** [get_top_letters rotors] is a string of the top letters of the
    oriented list [rotors].*)
let rec get_top_letters (rotors : oriented_rotor list) : string =
  match rotors with
  | [] -> ""
  | h :: k -> get_top_letters k ^ Char.escaped h.top_letter

(** [get_rotors config] is the oriented_rotor list field of [config]].*)
let get_rotors (config : config) : oriented_rotor list = config.rotors

(** [] *)
let step_test
    (name : string)
    (config : config)
    (expected_output : string) : test =
  name >:: fun _ ->
  assert_equal expected_output
    (config |> step |> get_rotors |> get_top_letters)
    ~printer:String.escaped

let cipher_test
    (name : string)
    (input_config : config)
    (input_s : string)
    (expected_output : string) : test =
  name >:: fun _ ->
  assert_equal expected_output
    (cipher input_config input_s)
    ~printer:String.escaped

(* You will find it helpful to write functions like [index_test] for
   each of the other functions you are testing. They will keep your
   lists of tests below very readable, and will also help you to avoid
   repeating code. You will also find it helpful to create [~printer]
   functions for the data types in use. *)

let index_tests =
  [
    index_test "index of A is 0" 'A' 0;
    index_test "index of B is 1" 'B' 1;
    index_test "index of Z is 25" 'Z' 25;
    index_test "index of R is 17" 'R' 17;
    index_test "index of M is 12" 'M' 12;
  ]

let map_rl_tests =
  [
    map_rl_test "(Baseline Test): No wiring, top letter A, input_pos 0"
      "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 'A' 0 0;
    map_rl_test "Custom rotor wiring, top letter A"
      "BACDEFGHIJKLMNOPQRSTUVWXYZ" 'A' 0 1;
    map_rl_test "Custom wiring, top letter B"
      "BACDEFGHIJKLMNOPQRSTUVWXYZ" 'B' 1 1;
    map_rl_test "Custom wiring, top letter B, input_pos 7"
      "BACDEFGHIJKLMNOPQRSTUVWXYZ" 'B' 7 7;
    map_rl_test "Rotor wiring 1, top letter A, input_pos 0"
      "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'A' 0 4;
    map_rl_test
      "Rotor 3 wiring, large Top letter O, large input_pos 14 "
      "BDFHJLCPRTXVZNYEIWGAKMUSQO" 'O' 14 17;
  ]

let map_lr_tests =
  [
    map_lr_test "(Baseline Test): No wiring, Top letter A, input_pos 0"
      "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 'A' 0 0;
    map_lr_test "Rotor wiring 1, base top letter A, input_pos 0"
      "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'A' 0 20;
    map_lr_test "Rotor wiring 1, Top letter B, input pos 0"
      "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'B' 0 21;
    map_lr_test "Rotor wiring 2, Top letter C, input pos 5"
      "AJDKSIRUXBLHWTMCQGZNPYFVOE" 'B' 0 8;
    map_lr_test "Rotor wiring 2, Top letter Z, input pos 25"
      "AJDKSIRUXBLHWTMCQGZNPYFVOE" 'Z' 0 19;
    map_lr_test "Rotor 3 wiring, large Top letter F, large input_pos 10"
      "EKMFLGDQVZNTOWYHXUSPAIBRCJ" 'F' 10 14;
  ]

let map_refl_tests =
  [
    map_refl_test "(Baseline Test): No reflection, input 0"
      "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 0 0;
    map_refl_test "No reflection, input 4" "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
      4 4;
    map_refl_test "Reflection, input 5" "YRUHQSLDPXNGOKMIEBFZCWVJAT" 5
      18;
    map_refl_test
      "Testing reverse reflection; 5 should map to 18, 18 should map \
       to 5"
      "YRUHQSLDPXNGOKMIEBFZCWVJAT" 18 5;
    map_refl_test "Testing for directionless reflection again"
      "FVPJIAOYEDRZXWGCTKUQSBNMHL" 3 9;
    map_refl_test "Testing for directionless reflection again"
      "FVPJIAOYEDRZXWGCTKUQSBNMHL" 9 3;
  ]

let plugboard_13 =
  [
    ('Z', 'A');
    ('P', 'B');
    ('O', 'X');
    ('N', 'D');
    ('M', 'E');
    ('S', 'F');
    ('W', 'G');
    ('C', 'H');
    ('I', 'R');
    ('Y', 'J');
    ('T', 'K');
    ('Q', 'L');
    ('U', 'V');
  ]

let map_plug_tests =
  [
    map_plug_test "empty plugboard" [] 'A' 'A';
    map_plug_test "1 plug" [ ('A', 'Z') ] 'A' 'Z';
    map_plug_test "Multiple plugs"
      [ ('A', 'Z'); ('C', 'M'); ('G', 'K') ]
      'G' 'K';
    map_plug_test "No plug for inputted char"
      [ ('A', 'Z'); ('C', 'M'); ('G', 'K') ]
      'B' 'B';
    map_plug_test "Reverse order of matching plug for inputted char"
      [ ('A', 'Z'); ('C', 'M'); ('G', 'K') ]
      'M' 'C';
    map_plug_test "Reverse order again "
      [ ('A', 'Z'); ('C', 'M'); ('G', 'K'); ('J', 'Y') ]
      'Y' 'J';
    map_plug_test "13 Plugs" plugboard_13 'K' 'T';
    map_plug_test "13 Plugs reverse order" plugboard_13 'T' 'K';
  ]

(*Components for Configs to test cipher_char*)
let rotor_I = { wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"; turnover = 'Q' }
let oriented_rotor_1_topA = { rotor = rotor_I; top_letter = 'A' }
let rotor_II = { wiring = "AJDKSIRUXBLHWTMCQGZNPYFVOE"; turnover = 'E' }
let oriented_rotor_2_topA = { rotor = rotor_II; top_letter = 'A' }

let rotor_III =
  { wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; turnover = 'V' }

let oriented_rotor_3_topA = { rotor = rotor_III; top_letter = 'A' }
let reflector_b = "YRUHQSLDPXNGOKMIEBFZCWVJAT"

let config_no_rotor =
  { refl = reflector_b; rotors = []; plugboard = plugboard_13 }

let config_2_rotors =
  {
    refl = reflector_b;
    rotors = [ oriented_rotor_3_topA; oriented_rotor_2_topA ];
    plugboard = plugboard_13;
  }

let config_4_rotors =
  {
    refl = reflector_b;
    rotors =
      [
        oriented_rotor_3_topA;
        oriented_rotor_2_topA;
        oriented_rotor_1_topA;
        oriented_rotor_2_topA;
      ];
    plugboard = plugboard_13;
  }

let ex_config =
  {
    refl = reflector_b;
    rotors =
      [
        oriented_rotor_1_topA;
        oriented_rotor_2_topA;
        oriented_rotor_3_topA;
      ];
    plugboard = [];
  }

let config_I =
  {
    refl = reflector_b;
    rotors =
      [
        oriented_rotor_1_topA;
        oriented_rotor_2_topA;
        oriented_rotor_3_topA;
      ];
    plugboard = plugboard_13;
  }

let cipher_char_tests =
  [
    cipher_char_test "Empty PB, Empty rotors, No refl"
      {
        refl = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        rotors = [];
        plugboard = [];
      }
      'A' 'A';
    cipher_char_test "Full PB, No rotors, refl" config_no_rotor 'C' 'N';
    cipher_char_test "Empty PB, 3 rotors, refl" ex_config 'G' 'P';
    cipher_char_test "Full PB, 3 rotors, refl" config_I 'R' 'G';
    cipher_char_test "Full PB, 2 rotors, refl" config_2_rotors 'Z' 'S';
    cipher_char_test "Full PB, 4 rotors, refl" config_4_rotors 'P' 'I';
  ]

let oriented_rotor_1_topO = { rotor = rotor_I; top_letter = 'O' }
let oriented_rotor_2_topD = { rotor = rotor_II; top_letter = 'D' }
let oriented_rotor_3_topK = { rotor = rotor_III; top_letter = 'K' }
let oriented_rotor_3_topU = { rotor = rotor_III; top_letter = 'U' }
let rotor_4 = { wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; turnover = 'Y' }
let oriented_rotor_4_topX = { rotor = rotor_4; top_letter = 'X' }

let main_config =
  {
    refl = reflector_b;
    rotors =
      [
        oriented_rotor_1_topO;
        oriented_rotor_2_topD;
        oriented_rotor_3_topK;
      ];
    plugboard = plugboard_13;
  }

let config_step_4 =
  {
    refl = reflector_b;
    rotors =
      [
        oriented_rotor_1_topO;
        oriented_rotor_2_topD;
        oriented_rotor_3_topU;
        oriented_rotor_4_topX;
      ];
    plugboard = plugboard_13;
  }

let wrap_config =
  {
    refl = reflector_b;
    rotors = [ oriented_rotor_4_topX; oriented_rotor_3_topK ];
    plugboard = plugboard_13;
  }

let or1 =
  {
    rotor = { wiring = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"; turnover = 'Q' };
    top_letter = 'F';
  }

let or2 =
  {
    rotor = { wiring = "AJDKSIRUXBLHWTMCQGZNPYFVOE"; turnover = 'E' };
    top_letter = 'U';
  }

let or3 =
  {
    rotor = { wiring = "BDFHJLCPRTXVZNYEIWGAKMUSQO"; turnover = 'V' };
    top_letter = 'N';
  }

let cipher_config =
  {
    refl = "YRUHQSLDPXNGOKMIEBFZCWVJAT";
    rotors = [ or3; or2; or1 ];
    plugboard = [ ('A', 'Z') ];
  }

let step_tests =
  [
    step_test "Rightmost rotor rotate (1 Step)" main_config "KDP";
    step_test "2 Steps" (main_config |> step) "KDQ";
    step_test "2nd rotor Step (3 Steps)"
      (main_config |> step |> step)
      "KER";
    step_test "3rd rotor Steps (4 Steps)"
      (main_config |> step |> step |> step)
      "LFS";
    step_test "5 Steps"
      (main_config |> step |> step |> step |> step)
      "LFT";
    step_test "6 Steps"
      (main_config |> step |> step |> step |> step |> step)
      "LFU";
    step_test "4th rotor Steps"
      (config_step_4 |> step |> step |> step |> step)
      "YWFT";
    step_test "Wrap around from Z to A (2 Rotors)"
      (wrap_config |> step |> step)
      "LA";
  ]

let main_config_no_PB =
  {
    refl = reflector_b;
    rotors =
      [
        oriented_rotor_1_topO;
        oriented_rotor_2_topD;
        oriented_rotor_3_topK;
      ];
    plugboard = [];
  }

let cipher_tests =
  [
    cipher_test "Initial Example" cipher_config "YNGXQ" "OCAML";
    cipher_test "Rotors 1,2,3 Refl b, no PB" main_config_no_PB "HELLO"
      "DOWWM";
    cipher_test "Rotors 1,2,3 Refl b, Full 13 PB" main_config "ROHIT"
      "FKJYH";
    cipher_test "Rotors 1,2,3 Refl b, 2 PB"
      { main_config with plugboard = [ ('A', 'B'); ('G', 'H') ] }
      "APPLE" "QKNWG";
    cipher_test "Rotors 1,2,3 Refl b, 1 PB"
      { main_config with plugboard = [ ('R', 'J') ] }
      "WATER" "FJJST";
  ]

let tests =
  "test suite for A1"
  >::: List.flatten
         [
           index_tests;
           map_rl_tests;
           map_lr_tests;
           map_refl_tests;
           map_plug_tests;
           cipher_char_tests;
           step_tests;
           cipher_tests;
         ]

let _ = run_test_tt_main tests
