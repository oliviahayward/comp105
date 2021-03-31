(* Olivia Hayward *)
(* Collaborated with Asiyah Mumuney *)

exception Mismatch;
exception Match;

(***** PART I *****)

val checkExpectInt        = Unit.checkExpectWith Unit.intString
val checkExpectIntList    = Unit.checkExpectWith
                                                (Unit.listString Unit.intString)
val checkExpectStringList = Unit.checkExpectWith
                                             (Unit.listString Unit.stringString)
val checkExpectISList =
  Unit.checkExpectWith (Unit.listString
                        (Unit.pairString Unit.intString Unit.stringString))
val checkExpectIntListList = 
  Unit.checkExpectWith (Unit.listString (Unit.listString Unit.intString))

val checkExpectIntPairList = Unit.checkExpectWith (Unit.listString
                        (Unit.pairString Unit.intString Unit.intString))


(***** Problem A *****)
(* mynull : 'a list -> bool *)
(* mynull checks whether a list is empty *)
fun   mynull [] = true
    | mynull xs = false;

        val () = 
            Unit.checkAssert "mynull Empty"
            (fn () => mynull [])
        
        val () = 
            Unit.checkAssert "mynull xs"
            (fn () => not (mynull [1, 2]))

(***** Problem B *****)
(* reverse : 'a list -> 'a list *)
(* reverse reverses the order of a list *)
fun   reverse [] = []
    | reverse xs = foldl op :: nil xs;

        val () = 
            checkExpectIntList "reverse empty"
            (fn () => reverse [])
            []
            
        val () = 
            checkExpectIntList "reverse [1, 2, 3]"
            (fn () => reverse [1, 2, 3])
            [3, 2, 1] 

(* minlist : int list -> int *)
(* minlist returns the smallest integer in a given list *)
fun   minlist []        = raise Match
    | minlist (x::xs)   = foldr Int.min x xs; 

        val () = 
            Unit.checkExpectWith Int.toString "minlist 4"
            (fn () => minlist [10, 9, 4])
            4
        
        val () = 
            Unit.checkExpectWith Int.toString "minlist -1"
            (fn () => minlist [~1, ~6, 5])
            ~6

(***** Problem C *****)
(* zip : 'a list * 'b list -> ('a * 'b) list *)
(* zip takes a pair of equal length lists and returns the equivalent list of *)
(* pairs *)
fun   zip ([], [])       = []
    | zip ([], y::ys)    = raise Mismatch
    | zip (x::xs, [])    = raise Mismatch
    | zip (x::xs, y::ys) = (x, y)::(zip (xs, ys));

        val () =
            checkExpectIntPairList "zip [[1, a], [3, a]]"
            (fn () => zip ([1, 3], [2, 4]))
            [(1, 2), (3, 4)]

(***** Problem D *****)

(* this function is just for testing purposes *)
fun threeArg (num1, num2, num3) = num1 + num2 + num3;

(* pairfoldrEq : ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c *)
(* pairfoldrEq applies a three-argument functio to a pair of equal length *)
(* lists *)
fun   pairfoldrEq func init ([], [])       = init
    | pairfoldrEq func init ((x::xs), (y::ys)) =
                                     func (x, y, pairfoldrEq func init (xs, ys))
    | pairfoldrEq func init _            = raise Mismatch;

        val () =
            checkExpectInt "pairfoldrEq plus 0 [1, 2] [3, 4]"
            (fn () => pairfoldrEq threeArg 0 ([1, 2], [3, 4]))
            10

(* ziptoo : 'a list * 'b list -> ('a * 'b) list *)
(* ziptoo takes a pair of equal length lists and returns the equivalent list *)
(* of pairs using pairfoldrEq *)
fun ziptoo (xs, ys) = pairfoldrEq (fn (x, y, zs) => (x, y) :: zs) [] (xs, ys);

        val () =
            checkExpectIntPairList "ziptoo [[1, 2], [3, 4]]"
            (fn () => ziptoo ([1, 3], [2, 4]))
            [(1, 2), (3, 4)]                                          

(***** Problem E *****)

(* concat : 'a list list -> 'a list *)
(* concat joins together every sublist in a list to one single list of *)
(* elements *)
fun   concat [] = []
    | concat xs = foldr List.@ nil xs;

        val () =
            checkExpectIntList "concat [1, 2, 3]"
            (fn () => concat [[1], [2, 3]])
            [1, 2, 3]

(***** PART II *****)

(***** Problem F *****)

datatype sx
  = SYMBOL of string
  | NUMBER of int
  | BOOL   of bool
  | SXLIST of sx list

fun sxString (SYMBOL s) = s
  | sxString (NUMBER n) = Int.toString n
  | sxString (BOOL b)   = if b then "true" else "false"
  | sxString (SXLIST sxs) = "(" ^ String.concatWith " "
                                                       (map sxString sxs) ^ ")";

(* numbersSx : 'a list -> sx list *)
(* numbersSx creates an ordinary S-expression given a list of numbers *)
fun numbersSx xs = (SXLIST (map NUMBER xs));

        val () =
            Unit.checkExpectWith  sxString "numbersSx [NUMBER 1 NUMBER 2]"
            (fn () => numbersSx [1, 2])
            (SXLIST [NUMBER 1, NUMBER 2])

(* flattenSyms : sx list -> list *)
(* flattenSyms extracts just the symbols from an ordinary S-expression *)
fun   flattenSyms (SYMBOL sx)      = [sx]
    | flattenSyms (SXLIST (x::xs)) = (flattenSyms x)@(flattenSyms (SXLIST xs))
    | flattenSyms _                = nil;

        val () =
            checkExpectStringList "flattenSyms [hi test]"
            (fn () => flattenSyms (SXLIST [(SYMBOL "hi"), (BOOL false),
                                                 (SXLIST []), (SYMBOL "test")]))
            ["hi", "test"]

(***** PART III *****)

datatype nat = ZERO
             | TIMES10PLUS of nat * int;

fun times10plus (ZERO, 0) = ZERO
  | times10plus (m, d)    = TIMES10PLUS (m, d);

(* times10 : nat -> nat *)
fun times10 n = times10plus (n, 0);

(* natOfDigit : int -> nat *)
fun natOfDigit d = times10plus (ZERO, d);

fun flip f (x, y) = f (y, x);

(* natOfDigits : int list -> nat *)
fun natOfDigits ds = foldl (flip times10plus) ZERO ds;

(***** Problem G *****)

(* intOfNat : nat -> int *)
(* intOfNat converts a natural number into a machine integer *)
fun   intOfNat ZERO = 0
    | intOfNat (TIMES10PLUS (m, d)) = (((intOfNat m) * 10) + d);

        val () = 
            Unit.checkExpectWith Int.toString "intOfNat 123"
            (fn () => intOfNat (natOfDigits [1, 2, 3]))
            123
        
        val () = 
            Unit.checkExpectWith Int.toString "intOfNat 0"
            (fn () => intOfNat (natOfDigits [0]))
            0

(* natString : nat -> string *)
(* natString converts a natural number into a string *)
fun   natString ZERO                 = "0"
    | natString (TIMES10PLUS (ZERO, d)) = Int.toString d
    | natString (TIMES10PLUS (m, d)) = (natString m) ^ Int.toString d;

    val () = 
            Unit.checkExpectWith String.toString "natString 1"
            (fn () => natString (TIMES10PLUS(ZERO, 1)))
            "1"

(* natOfInt : int -> nat *)
(* natOfInt converts a machine integer into a natural number *)
fun   natOfInt 0 = ZERO
    | natOfInt x = (TIMES10PLUS ((natOfInt (x div 10)), (x mod 10)));

    val () = 
            Unit.checkExpectWith String.toString "natOfInt 2018"
            (fn () => natString(natOfInt (2018)))
            "2018"

(***** Problem H *****)

exception Negative;
exception NotABit;

(* carryIntoNat : nat * int -> nat *)
(* carryIntoNat returns the sum of a natural number and carry bit *)
fun   carryIntoNat (TIMES10PLUS (m, d), 0) = TIMES10PLUS (m, d)
    | carryIntoNat (ZERO, c) = (natOfInt c)
    | carryIntoNat (TIMES10PLUS (m, d), 1) = times10plus
                                               (carryIntoNat (m, (d + 1) div 10)
                                                            , ((d + 1) mod 10))
    | carryIntoNat (TIMES10PLUS (m, d), _)           = raise NotABit;


(* addWithCarry : nat * nat * int -> nat *)
(* addWithCarry returns the sum of two natural numbers and a carry bit *)
fun   addWithCarry (TIMES10PLUS (m, d), ZERO, c) = 
                                            carryIntoNat (TIMES10PLUS (m, d), c)
    | addWithCarry (ZERO, TIMES10PLUS (m, d), c) =
                                            carryIntoNat (TIMES10PLUS (m, d), c)
    | addWithCarry (TIMES10PLUS (m1, d1), TIMES10PLUS (m2, d2), c) = 
                    times10plus ((addWithCarry (m1, m2, (d1 + d2 + c) div 10)),
                                                          (d1 + d2 + c) mod 10)
    | addWithCarry (ZERO, ZERO, c) = (natOfInt c);

(* addNats : nat * nat -> nat *)
(* addNats adds two natural numbers together *)
fun addNats (n1, n2) = addWithCarry (n1, n2, 0);

(* borrowFromNat : nat * int -> nat *)
(* borrowFromNat returns the subtraction of a carry bit from a natural number *)
fun   borrowFromNat (n, 0) = n 
    | borrowFromNat (TIMES10PLUS (m, 0), 1) = times10plus (borrowFromNat (m, 1)
                                                                            , 9)
    | borrowFromNat (TIMES10PLUS (m, d), 1) = times10plus (m, (d - 1))
    | borrowFromNat (TIMES10PLUS (m, d), _) = raise NotABit
    | borrowFromNat (ZERO, 1) = raise Negative
    | borrowFromNat (n, _) = raise NotABit;

(* subWithBorrow : nat * nat * int -> nat *)
(* subWithBorrow returns the subtraction of a carry bit from the subtraction *)
(* of two natural numbers *)
fun   subWithBorrow (n1, ZERO, b) = borrowFromNat (n1, b)
    | subWithBorrow (TIMES10PLUS (m1, d1), TIMES10PLUS (m2, d2), b) = 
        let val d  = (d1 - d2 - b) mod 10
            val b' = if d1 - d2 - b < 0 then 1 else 0
        in  times10plus (subWithBorrow (m1, m2, b'), (d1 - d2 - b) mod 10)
        end
    | subWithBorrow _ = raise Negative;

(* subNats : nat * nat -> nat *)
(* subNats subtracts a natural number from another natural number *)
fun subNats (n1, n2) = subWithBorrow (n1, n2, 0);

fun opsAgree name intop natop n1 n2 =
  Unit.checkExpectWith Int.toString name
  (fn () => intOfNat (natop (natOfInt n1, natOfInt n2)))
  (intop (n1, n2) handle Overflow => 0)

val () = opsAgree "123 + 2018" (op +)  addNats 123 2018
val () = opsAgree "2018 - 123" (op -)  subNats 2018 123
val () = opsAgree "100 - 1   " (op -)  subNats 100 1

val () = Unit.reportWhenFailures ()  (* put me at the _end_ *)