let and: Bool -> Bool -> Bool =
  lam a90: Bool.
    lam b30: Bool.
      match a90 with true
      then
        b30
      else
        false
in
let isNaN: Float -> Bool =
  lam a89: Float.
    match eqf a89 a89 with true
    then
      false
    else
      true
in
external externalExp : Float -> Float in
let exp = lam x164: Float.
    externalExp x164 in
external externalLog : Float -> Float in
let log = lam x163: Float.
    externalLog x163 in
external externalPow : Float -> Float -> Float in
let pow = lam x162: Float.
    lam y: Float.
      externalPow x162 y
in
recursive
  let rec: all a. all a1. (a -> a1) -> [a] -> [a1] =
    lam f.
      lam s.
        match s with ""
        then
          ""
        else match s with [ a2 ]
        then
          [ f a2 ]
        else match s with [ a3 ] ++ ss
        in
        cons (f a3) (rec f ss)
in
let map1 = lam f28.
    lam s14.
      rec f28 s14 in
recursive
  let rec1: all a4. all a5. (Int -> a4 -> a5) -> Int -> [a4] -> [a5] =
    lam f1.
      lam i.
        lam s1.
          match s1 with ""
          then
            ""
          else match s1 with [ a6 ]
          then
            [ f1 i a6 ]
          else match s1 with [ a7 ] ++ ss1
          in
          cons (f1 i a7) (rec1 f1 (addi i 1) ss1)
in
let mapi1 = lam f27.
    lam s13.
      rec1 f27 0 s13 in
let iteri1 =
  lam f26.
    lam s12.
      let #var"17" = mapi1 f26 s12 in
      {}
in
recursive
  let rec2: all a8. all a9. (a8 -> a9 -> a8) -> a8 -> [a9] -> a8 =
    lam f2.
      lam acc.
        lam s2.
          match s2 with ""
          then
            acc
          else match s2 with [ a10 ] ++ ss2
          in
          rec2 f2 (f2 acc a10) ss2
in
let foldl1 =
  lam f25.
    lam acc21.
      lam s11.
        rec2 f25 acc21 s11
in
recursive
  let rec3: all a11. (Int -> a11) -> Int -> [a11] -> [a11] =
    lam f3.
      lam i1.
        lam acc1.
          match geqi i1 0 with true
          then
            rec3 f3 (subi i1 1) (cons (f3 i1) acc1)
          else
            acc1
in
let create1 = lam l9.
    lam f24.
      rec3 f24 (subi l9 1) ""
in
type Option a12 in
con Some: all a13. a13 -> Option a13 in
con None: all a14. () -> Option a14 in
type Either a15 b in
con Left: all a16. all b1. a16 -> Either a16 b1 in
con Right: all a17. all b2. b2 -> Either a17 b2 in
let anon: all a88. a88 -> Int -> a88 = lam v2.
    lam #var"16".
      v2
in
let make: all a87. Int -> a87 -> [a87] = lam n5: Int.
    lam v1: a87.
      create1 n5 (anon v1)
in
recursive
  let unfoldr: all a18. all c. (a18 -> Option (c, a18)) -> a18 -> [c] =
    lam f4: a18 -> Option (c, a18).
      lam b0: a18.
        let fb = f4 b0 in
        match fb with None _
        then
          ""
        else match fb with Some (x, b11)
        in
        cons x (unfoldr f4 b11)
in
let anon1: Int -> Int -> Int -> Option (Int, Int) =
  lam e4.
    lam by1.
      lam b29.
        match leqi e4 b29 with true
        then
          None
            {}
        else
          Some
            (b29, addi b29 by1)
in
let range: Int -> Int -> Int -> [Int] =
  lam s10: Int.
    lam e3: Int.
      lam by: Int.
        unfoldr (anon1 e3 by) s10
in
let g: all c13. all b28. all a86. (a86 -> b28 -> c13 -> a86) -> (a86, [b28]) -> c13 -> (a86, [b28]) =
  lam f23.
    lam acc19: (a86, [b28]).
      lam x212.
        match acc19 with (acc20, [ x161 ] ++ xs1)
        then
          (f23 acc20 x161 x212, xs1)
        else
          error "foldl2: Cannot happen!"
in
let g1: all c12. all b27. all a85. (a85 -> b27 -> c12 -> a85) -> (a85, [c12]) -> b27 -> (a85, [c12]) =
  lam f22.
    lam acc17: (a85, [c12]).
      lam x160.
        match acc17 with (acc18, [ x211 ] ++ xs2)
        then
          (f22 acc18 x160 x211, xs2)
        else
          error "foldl2: Cannot happen!"
in
let foldl2: all a84. all b26. all c11. (a84 -> b26 -> c11 -> a84) -> a84 -> [b26] -> [c11] -> a84 =
  lam f21: a84 -> b26 -> c11 -> a84.
    lam acc14: a84.
      lam seq11: [b26].
        lam seq21: [c11].
          match geqi (length seq11) (length seq21) with true
          then
            match foldl1 (g f21) (acc14, seq11) seq21 with (acc15, _)
            in
            acc15
          else match foldl1 (g1 f21) (acc14, seq21) seq11 with (acc16, _)
          in
          acc16
in
recursive
  let work: all b3. all a19. (a19 -> Int -> b3 -> a19) -> a19 -> Int -> [b3] -> a19 =
    lam fn.
      lam acc2.
        lam i2.
          lam s3.
            match s3 with [ e ] ++ rest
            then
              work fn (fn acc2 i2 e) (addi i2 1) rest
            else
              acc2
in
let foldli: all a83. all b25. (a83 -> Int -> b25 -> a83) -> a83 -> [b25] -> a83 =
  lam fn1: a83 -> Int -> b25 -> a83.
    lam initAcc: a83.
      lam seq9: [b25].
        work fn1 initAcc 0 seq9
in
let anon2: all c10. all b24. all a82. (a82 -> b24 -> c10) -> [c10] -> a82 -> b24 -> [c10] =
  lam f20.
    lam acc13.
      lam x159.
        lam x210.
          snoc acc13 (f20 x159 x210)
in
let zipWith: all a81. all b23. all c9. (a81 -> b23 -> c9) -> [a81] -> [b23] -> [c9] = lam f19: a81 -> b23 -> c9.
    foldl2 (anon2 f19) ""
in
recursive
  let any: all a20. (a20 -> Bool) -> [a20] -> Bool =
    lam p: a20 -> Bool.
      lam seq: [a20].
        match null seq with true
        then
          false
        else match p (head seq) with true
        then
          true
        else
          any p (tail seq)
in
let join: all a80. [[a80]] -> [a80] = lam seqs: [[a80]].
    foldl1 concat "" seqs
in
recursive
  let work1: all a21. (a21 -> Bool) -> [a21] -> [a21] -> [a21] -> ([a21], [a21]) =
    lam p1.
      lam l.
        lam r.
          lam seq1.
            match seq1 with ""
            then
              (l, r)
            else match seq1 with [ s4 ] ++ seq2
            in
            match p1 s4 with true
            then
              work1 p1 (cons s4 l) r seq2
            else
              work1 p1 l (cons s4 r) seq2
in
let partition: all a79. (a79 -> Bool) -> [a79] -> ([a79], [a79]) =
  lam p4: a79 -> Bool.
    lam seq8: [a79].
      work1 p4 "" "" (reverse seq8)
in
let anon3: all a78. (a78 -> a78 -> Int) -> a78 -> a78 -> Bool =
  lam cmp4.
    lam h4.
      lam x158.
        lti (cmp4 x158 h4) 0
in
recursive
  let quickSort: all a22. (a22 -> a22 -> Int) -> [a22] -> [a22] =
    lam cmp: a22 -> a22 -> Int.
      lam seq3: [a22].
        match null seq3 with true
        then
          seq3
        else
          let h = head seq3 in
          let t = tail seq3 in
          let lr = partition (anon3 cmp h) t in
          concat (quickSort cmp lr.0) (cons h (quickSort cmp lr.1))
in
let eitherEither: all a77. all b22. all c8. (a77 -> c8) -> (b22 -> c8) -> Either a77 b22 -> c8 =
  lam lf: a77 -> c8.
    lam rf: b22 -> c8.
      lam e2: Either a77 b22.
        match e2 with Left content
        then
          lf content
        else match e2 with Right content1
        in
        rf content1
in
type ExtArrKind a23 in
type ExtArr a24 in
external externalExtArrMakeUninit : all a25. ExtArrKind a25 -> Int -> ExtArr a25
in
external externalExtArrKind : all a26. ExtArr a26 -> ExtArrKind a26
in
external externalExtArrLength : all a27. ExtArr a27 -> Int in
external externalExtArrGet : all a28. ExtArr a28 -> Int -> a28
in
external externalExtArrSet! : all a29. ExtArr a29 -> Int -> a29 -> ()
in
external extArrKindFloat64 : ExtArrKind Float in
let extArrLength: all a75. ExtArr a75 -> Int = lam a76: ExtArr a75.
    externalExtArrLength a76
in
let extArrGetExn: all a73. ExtArr a73 -> Int -> a73 =
  lam a74: ExtArr a73.
    lam i21: Int.
      externalExtArrGet a74 i21
in
let extArrOfSeq: all a71. ExtArrKind a71 -> [a71] -> ExtArr a71 =
  lam kind1: ExtArrKind a71.
    lam seq7: [a71].
      tmOpaque (let len = length seq7 in
       let a72 = externalExtArrMakeUninit kind1 len in
       recursive
         let work3 =
           lam i20.
             match eqi i20 len with true
             then
               {}
             else
               let #var"14" = externalExtArrSet a72 i20 (get seq7 i20) in
               work3 (addi i20 1)
       in
       let #var"15" = work3 0 in
       a72)
in
type CBLASLayout in
external cblasRowMajor : CBLASLayout in
type CBLASTranspose in
external cblasNoTrans : CBLASTranspose in
external externalCblasCopy : all a30. Int -> ExtArr a30 -> Int -> ExtArr a30 -> Int -> ()
in
external externalCblasScal : all a31. Int -> a31 -> ExtArr a31 -> Int -> ()
in
external externalCblasGemm : all a32. CBLASLayout -> CBLASTranspose -> CBLASTranspose -> Int -> Int -> Int -> a32 -> ExtArr a32 -> Int -> ExtArr a32 -> Int -> a32 -> ExtArr a32 -> Int -> ()
in
type MatError in
con DimensionMismatch: () -> MatError in
con NotSquare: () -> MatError in
let matErrorToString: MatError -> [Char] =
  lam err3: MatError.
    let #var"X13" = err3 in
    match #var"X13" with DimensionMismatch _
    then
      "Dimension mismatch"
    else match #var"X13" with NotSquare _
    in
    "Not square"
in
type Mat a33 =
  {m: Int, n: Int, arr: ExtArr a33} in
let matMakeUninit: all a70. ExtArrKind a70 -> Int -> Int -> Mat a70 =
  lam kind: ExtArrKind a70.
    lam m3: Int.
      lam n4: Int.
        { n = n4,
          arr = externalExtArrMakeUninit kind (muli m3 n4),
          m = m3 }
in
let matGetExn: all a68. Mat a68 -> Int -> Int -> a68 =
  lam a69: Mat a68.
    lam i19: Int.
      lam j1: Int.
        externalExtArrGet a69.arr (addi (muli i19 a69.n) j1)
in
let matSetExn: all a66. Mat a66 -> Int -> Int -> a66 -> () =
  lam a67: Mat a66.
    lam i18: Int.
      lam j: Int.
        lam v: a66.
          externalExtArrSet a67.arr (addi (muli i18 a67.n) j) v
in
let matFromArrExn: all a64. Int -> Int -> ExtArr a64 -> Mat a64 =
  lam m2: Int.
    lam n3: Int.
      lam a65: ExtArr a64.
        match eqi (muli m2 n3) (extArrLength a65) with true
        then
          { n = n3, arr = a65, m = m2 }
        else
          error "matFromArrExn: dimensions mismatch"
in
let matHasSameShape2 =
  lam a63.
    lam b21.
      and (eqi a63.m b21.m) (eqi a63.n b21.n)
in
let matHasSameShape3 =
  lam a62.
    lam b20.
      lam c7.
        and (matHasSameShape2 a62 b20) (matHasSameShape2 b20 c7)
in
let matIsSquare = lam a61.
    eqi a61.m a61.n in
external externalMatTranspose : Int -> Int -> ExtArr Float -> ExtArr Float -> ()
in
let matTranposeNoAlloc: Mat Float -> Mat Float -> Either MatError () =
  lam a60: Mat Float.
    lam b19: Mat Float.
      match and (eqi a60.m b19.n) (eqi a60.n b19.m) with true
      then
        let #var"13" = externalMatTranspose a60.m a60.n a60.arr b19.arr
        in
        Right
          {}
      else
        Left
          (DimensionMismatch
             {})
in
external externalMatElemMul : Int -> Int -> ExtArr Float -> ExtArr Float -> ExtArr Float -> ()
in
let matElemMulNoAlloc: Mat Float -> Mat Float -> Mat Float -> Either MatError () =
  lam a59: Mat Float.
    lam b18: Mat Float.
      lam c6: Mat Float.
        match matHasSameShape3 a59 b18 c6 with true
        then
          let #var"12" = externalMatElemMul a59.m a59.n a59.arr b18.arr c6.arr
          in
          Right
            {}
        else
          Left
            (DimensionMismatch
               {})
in
let matTranspose: Mat Float -> Mat Float =
  lam a58: Mat Float.
    tmOpaque (let b17 = matMakeUninit (externalExtArrKind a58.arr) a58.n a58.m
     in
     let #var"11" = matTranposeNoAlloc a58 b17 in
     b17)
in
let matElemMul: Mat Float -> Mat Float -> Either MatError (Mat Float) =
  lam a57: Mat Float.
    lam b16: Mat Float.
      match matHasSameShape2 a57 b16 with true
      then
        Right
          (tmOpaque (let c5 = matMakeUninit (externalExtArrKind a57.arr) a57.m a57.n
            in
            let #var"10" = matElemMulNoAlloc a57 b16 c5 in
            c5))
      else
        Left
          (DimensionMismatch
             {})
in
let anon4: MatError -> Mat Float = lam err2.
    error (matErrorToString err2)
in
let anon5: Mat Float -> Mat Float = lam x157.
    x157 in
let matElemMulExn: Mat Float -> Mat Float -> Mat Float =
  lam a56: Mat Float.
    lam b15: Mat Float.
      eitherEither anon4 anon5 (matElemMul a56 b15)
in
let matScale: Float -> Mat Float -> Mat Float =
  lam s9: Float.
    lam a55: Mat Float.
      let m1 = a55.m in
      let n2 = a55.n in
      let mn = muli m1 n2 in
      tmOpaque (let b14 = matMakeUninit (externalExtArrKind a55.arr) m1 n2 in
       let #var"8" = externalCblasCopy mn a55.arr 1 b14.arr 1 in
       let #var"9" = externalCblasScal mn s9 b14.arr 1 in
       b14)
in
let matMul: Mat Float -> Mat Float -> Either MatError (Mat Float) =
  lam a54: Mat Float.
    lam b13: Mat Float.
      let m = a54.m in
      let n1 = b13.n in
      let k2 = a54.n in
      match eqi k2 b13.m with true
      then
        Right
          (tmOpaque (let c4 = matMakeUninit (externalExtArrKind b13.arr) m n1 in
            let #var"7" =
              externalCblasGemm
                cblasRowMajor
                cblasNoTrans
                cblasNoTrans
                m
                n1
                k2
                1.
                a54.arr
                k2
                b13.arr
                n1
                0.
                c4.arr
                n1
            in
            c4))
      else
        Left
          (DimensionMismatch
             {})
in
let anon6: MatError -> Mat Float = lam err1.
    error (matErrorToString err1)
in
let anon7: Mat Float -> Mat Float = lam x156.
    x156 in
let matMulExn: Mat Float -> Mat Float -> Mat Float =
  lam a53: Mat Float.
    lam b12: Mat Float.
      eitherEither anon6 anon7 (matMul a53 b12)
in
external externalMatExp : Int -> Int -> ExtArr Float -> ExtArr Float
in
let matExp: Mat Float -> Either MatError (Mat Float) =
  lam a52: Mat Float.
    match matIsSquare a52 with true
    then
      Right
        { a52 with arr = externalMatExp a52.m a52.n a52.arr }
    else
      Left
        (NotSquare
           {})
in
let anon8: MatError -> Mat Float = lam err.
    error (matErrorToString err)
in
let anon9: Mat Float -> Mat Float = lam x155.
    x155 in
let matExpExn: Mat Float -> Mat Float =
  lam a51: Mat Float.
    eitherEither anon8 anon9 (matExp a51)
in
recursive
  let work2: all a34. Int -> (Int -> a34 -> a34) -> Int -> a34 -> a34 =
    lam bound.
      lam f5.
        lam i3.
          lam acc3.
            match lti i3 bound with true
            then
              work2 bound f5 (addi i3 1) (f5 i3 acc3)
            else
              acc3
in
let _iterateni = lam bound1.
    lam f18.
      work2 bound1 f18 0
in
let seqSnoc = snoc in
let seqCons = cons in
let seqLength = length in
let seqMap = map1 in
let seqZipWith = zipWith in
let seqSubsequence = subsequence in
let seqFoldl = foldl1 in
let seqFoldli = foldli in
let seqAny = any in
let mathExp = exp in
let mathLog = log in
let anon10: Matrix Float -> Int -> Float -> Float =
  lam t4.
    lam i17.
      lam acc12.
        addf acc12 (extArrGetExn t4.arr i17)
in
let matMean =
  lam t3.
    let sum = _iterateni (muli t3.m t3.n) (anon10 t3) 0. in
    divf sum (int2float (muli t3.m t3.n))
in
let anon11: all a50. Mat a50 -> Int -> Mat a50 -> Int -> Int -> () =
  lam matrix1.
    lam r6.
      lam new1.
        lam i16.
          lam c3.
            matSetExn new1 0 i16 (matGetExn matrix1 r6 (subi c3 1))
in
let matRowCols =
  lam matrix.
    lam row3.
      lam cols3.
        let r5 = subi row3 1 in
        let new =
          matMakeUninit (externalExtArrKind matrix.arr) 1 (length cols3)
        in
        let #var"6" = iteri1 (anon11 matrix r5 new) cols3 in
        new
in
type Matrix #var"X" =
  Mat #var"X" in
let x1: all #var"B10". all #var"A10". (#var"A10" -> #var"B10" -> #var"A10") -> #var"A10" -> #var"B10" -> #var"A10" =
  lam f17.
    lam a49.
      lam b10: #var"B10".
        let x154: #var"A10" = f17 a49 b10 in
        x154
in
let x2: all #var"B9". all #var"A9". (#var"A9" -> Int -> #var"B9" -> #var"A9") -> #var"A9" -> Int -> #var"B9" -> #var"A9" =
  lam f16.
    lam a48.
      lam idx7.
        lam b9: #var"B9".
          let x153: #var"A9" = f16 a48 (addi idx7 1) b9 in
          x153
in
let x3: all #var"B8". all #var"A8". (#var"A8" -> Int -> #var"B8" -> #var"A8") -> #var"A8" -> Int -> #var"B8" -> #var"A8" =
  lam f15.
    lam a47.
      lam idx6: Int.
        x2 f15 a47 idx6
in
let x4: all #var"C2". all #var"B7". all #var"A7". (#var"A7" -> #var"B7" -> #var"C2") -> #var"A7" -> #var"B7" -> #var"C2" =
  lam f14.
    lam a46.
      lam b8: #var"B7".
        let x152: #var"C2" = f14 a46 b8 in
        x152
in
let x5: all #var"X12". (#var"X12" -> #var"X12" -> Int) -> #var"X12" -> #var"X12" -> Int =
  lam cmp3.
    lam a45.
      lam b7: #var"X12".
        let x151: Int = cmp3 a45 b7 in
        x151
in
let exp1: Float -> Float = lam x150: Float.
    mathExp x150 in
let log1: Float -> Float = lam x149: Float.
    mathLog x149 in
let cons1: all #var"X11". #var"X11" -> [#var"X11"] -> [#var"X11"] =
  lam e1: #var"X11".
    lam s8: [#var"X11"].
      seqCons e1 s8
in
let rep: all #var"X10". Int -> #var"X10" -> [#var"X10"] =
  lam count: Int.
    lam elem1: #var"X10".
      make count elem1
in
let paste0: all #var"X9". [[#var"X9"]] -> [#var"X9"] = lam l8: [[#var"X9"]].
    join l8
in
let slice: all #var"X8". [#var"X8"] -> Int -> Int -> [#var"X8"] =
  lam l7: [#var"X8"].
    lam first: Int.
      lam last: Int.
        seqSubsequence l7 (subi first 1) (subi last first)
in
let length1: all #var"X7". [#var"X7"] -> Int = lam l6: [#var"X7"].
    seqLength l6
in
let sapply: all #var"A6". all #var"B6". [#var"A6"] -> (#var"A6" -> #var"B6") -> [#var"B6"] =
  lam s7: [#var"A6"].
    lam f13: #var"A6" -> #var"B6".
      seqMap f13 s7
in
let anon12: all #var"B5". all #var"A5". (#var"A5" -> #var"B5" -> #var"A5") -> #var"A5" -> #var"B5" -> #var"A5" = lam f12.
    lam a44: #var"A5".
      x1 f12 a44
in
let fold: all #var"A4". all #var"B4". (#var"A4" -> #var"B4" -> #var"A4") -> #var"A4" -> [#var"B4"] -> #var"A4" =
  lam f11: #var"A4" -> #var"B4" -> #var"A4".
    lam init1: #var"A4".
      lam seq6: [#var"B4"].
        seqFoldl (anon12 f11) init1 seq6
in
let anon13: all #var"B3". all #var"A3". (#var"A3" -> Int -> #var"B3" -> #var"A3") -> #var"A3" -> Int -> #var"B3" -> #var"A3" = lam f10.
    lam a43: #var"A3".
      x3 f10 a43
in
let foldi: all #var"A2". all #var"B2". (#var"A2" -> Int -> #var"B2" -> #var"A2") -> #var"A2" -> [#var"B2"] -> #var"A2" =
  lam f9: #var"A2" -> Int -> #var"B2" -> #var"A2".
    lam init: #var"A2".
      lam seq5: [#var"B2"].
        seqFoldli (anon13 f9) init seq5
in
let anon14: all #var"C1". all #var"B1". all #var"A1". (#var"A1" -> #var"B1" -> #var"C1") -> #var"A1" -> #var"B1" -> #var"C1" = lam f8.
    lam a42: #var"A1".
      x4 f8 a42
in
let zipWith1: all #var"A". all #var"B". all #var"C". (#var"A" -> #var"B" -> #var"C") -> [#var"A"] -> [#var"B"] -> [#var"C"] =
  lam f7: #var"A" -> #var"B" -> #var"C".
    lam a41: [#var"A"].
      lam b6: [#var"B"].
        seqZipWith (anon14 f7) a41 b6
in
let any1: all #var"X6". (#var"X6" -> Bool) -> [#var"X6"] -> Bool =
  lam f6: #var"X6" -> Bool.
    lam l5: [#var"X6"].
      seqAny f6 l5
in
let anon15: all #var"X5". (#var"X5" -> #var"X5" -> Int) -> #var"X5" -> #var"X5" -> Int = lam cmp2.
    lam a40: #var"X5".
      x5 cmp2 a40
in
let qSort: all #var"X4". (#var"X4" -> #var"X4" -> Int) -> [#var"X4"] -> [#var"X4"] =
  lam cmp1: #var"X4" -> #var"X4" -> Int.
    lam l4: [#var"X4"].
      quickSort (anon15 cmp1) l4
in
let anon16: [Int] -> Int -> Bool -> [Int] =
  lam acc11: [Int].
    lam idx5: Int.
      lam elem: Bool.
        let x148: [Int] =
          match elem with true
          then
            seqSnoc acc11 idx5
          else
            acc11
        in
        x148
in
let whichTrue: [Bool] -> [Int] = lam s6: [Bool].
    foldi anon16 "" s6
in
let mtxCreate: Int -> Int -> [Float] -> Matrix Float =
  lam rows1: Int.
    lam cols2: Int.
      lam data: [Float].
        matFromArrExn rows1 cols2 (extArrOfSeq extArrKindFloat64 data)
in
let mtxGet: all #var"X3". Int -> Int -> Matrix #var"X3" -> #var"X3" =
  lam row2: Int.
    lam col: Int.
      lam mtx6: Matrix #var"X3".
        matGetExn mtx6 (subi row2 1) (subi col 1)
in
let mtxRowCols: all #var"X2". Matrix #var"X2" -> Int -> [Int] -> Matrix #var"X2" =
  lam mtx5: Matrix #var"X2".
    lam row1: Int.
      lam cols1: [Int].
        matRowCols mtx5 row1 cols1
in
let mtxSclrMul: Float -> Matrix Float -> Matrix Float =
  lam scalar: Float.
    lam mtx4: Matrix Float.
      matScale scalar mtx4
in
let mtxTrans: Matrix Float -> Matrix Float = lam mtx3: Matrix Float.
    matTranspose mtx3
in
let mtxExp: Matrix Float -> Matrix Float = lam mtx2: Matrix Float.
    matExpExn mtx2
in
let mtxMul: Matrix Float -> Matrix Float -> Matrix Float =
  lam a39: Matrix Float.
    lam b5: Matrix Float.
      matMulExn a39 b5
in
let mtxElemMul: Matrix Float -> Matrix Float -> Matrix Float =
  lam a38: Matrix Float.
    lam b4: Matrix Float.
      matElemMulExn a38 b4
in
let mtxMean: Matrix Float -> Float = lam mtx1: Matrix Float.
    matMean mtx1
in
let mathIsNaN = isNaN in
let row: all a37. [a37] -> Int -> Int -> [a37] =
  lam l3.
    lam c2.
      lam i15.
        let rs = muli i15 c2 in
        let re = addi rs c2 in
        subsequence l3 rs c2
in
let seqNest: all a36. [a36] -> Int -> Int -> [[a36]] =
  lam l2: [a36].
    lam r4: Int.
      lam c1: Int.
        map1 (row l2 c1) (range 0 r4 1)
in
let delta =
  lam k1.
    lam x147.
      match eqi k1 x147 with true
      then
        1.
      else
        0.
in
let seqKroneckerDelta: Int -> Int -> [Float] =
  lam i14: Int.
    lam n: Int.
      let k = subi i14 1 in
      map1 (delta k) (range 0 n 1)
in
let nestSeq: all #var"X1". [#var"X1"] -> Int -> Int -> [[#var"X1"]] =
  lam seq4: [#var"X1"].
    lam rows: Int.
      lam cols: Int.
        seqNest seq4 rows cols
in
let kroneckerDelta: Int -> Int -> [Float] =
  lam index: Int.
    lam length2: Int.
      seqKroneckerDelta index length2
in
let isNaN1: Float -> Bool = lam r3: Float.
    mathIsNaN r3 in
type TreeLabeled in
type MsgTree in
type ModelParams in
type HistoryTree in
type Event in
type BranchSample in
type HostBranchSample in
type CorrectedBranchSample in
type EmbeddedMarkovChainMatrix in
con Leaf: {age: Float, label: Int} -> TreeLabeled in
con Node: {age: Float, left: TreeLabeled, label: Int, right: TreeLabeled} -> TreeLabeled
in
con MsgLeaf: {age: Float, label: Int, outMsg: Matrix Float, interactions: [Int]} -> MsgTree
in
con MsgNode: {age: Float, left: MsgTree, label: Int, right: MsgTree, outMsg: Matrix Float, leftInMsg: Matrix Float, leftKernel: Matrix Float, rightInMsg: Matrix Float, rightKernel: Matrix Float} -> MsgTree
in
con ModelParams1: {beta: Float, meanDist: Float, hostMetric: Matrix Float, embeddedQMatrix: EmbeddedMarkovChainMatrix} -> ModelParams
in
con HistoryLeaf: {age: Float, label: Int, history: [Event], repertoire: [Int]} -> HistoryTree
in
con HistoryNode: {age: Float, left: HistoryTree, label: Int, right: HistoryTree, history: [Event], repertoire: [Int]} -> HistoryTree
in
con Event1: {host: Int, toState: Int, eventTime: Float, fromState: Int} -> Event
in
con BranchSample1: {history: [[Event]], success: Bool} -> BranchSample
in
con HostBranchSample1: {history: [Event], success: Bool} -> HostBranchSample
in
con CorrectedBranchSample1: {history: [Event], logDebt: Float, success: Bool, logExcess: Float} -> CorrectedBranchSample
in
con EmbeddedMarkovChainMatrix1: {mat: Matrix Float, totalRates: [Float], transitionProbs: [[Float]]} -> EmbeddedMarkovChainMatrix
in
let rateMatrixToEmbeddedMarkovChain: Matrix Float -> EmbeddedMarkovChainMatrix =
  lam qMatrix2: Matrix Float.
    let q1 = negf (mtxGet 1 1 qMatrix2) in
    let q2 = negf (mtxGet 2 2 qMatrix2) in
    let q3 = negf (mtxGet 3 3 qMatrix2) in
    EmbeddedMarkovChainMatrix1
      { totalRates = [ q1,
            q2,
            q3 ],
        transitionProbs =
          [ [ 0., 1., 0. ],
            [ divf (mtxGet 2 1 qMatrix2) q2,
              0.,
              divf (mtxGet 2 3 qMatrix2) q2 ],
            [ 0., 1., 0. ] ],
        mat = qMatrix2 }
in
let is2: Int -> Bool = lam x146: Int.
    eqi x146 2 in
recursive
  let ones: Int -> [Float] =
    lam nOnes: Int.
      match gti nOnes 0 with true
      then
        cons1 1. (ones (subi nOnes 1))
      else
        ""
in
let anon17: Int -> Int -> Int =
  lam acc10: Int.
    lam h3: Int.
      let x145: Int =
        match eqi h3 2 with true
        then
          addi acc10 1
        else
          acc10
      in
      x145
in
let n2s: [Int] -> Int = lam repertoire2: [Int].
    fold anon17 0 repertoire2
in
let updateRepertoire: [Int] -> Event -> Int -> [Int] =
  lam currRep7: [Int].
    lam event2: Event.
      lam nhosts11: Int.
        let hostIndex4 =
          let target89 = event2 in
          match target89 with Event1 x144
          then
            x144.host
          else
            (print
                 "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n")
            ; exit 1
        in
        paste0
          [ slice currRep7 1 hostIndex4,
            [ let target88 = event2 in
              match target88 with Event1 x143
              then
                x143.toState
              else
                (print
                     "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n")
                ; exit 1 ],
            slice currRep7 (addi hostIndex4 1) (addi nhosts11 1) ]
in
let sampleNextEvent: Int -> EmbeddedMarkovChainMatrix -> Int =
  lam currState1: Int.
    lam embeddedQMatrix4: EmbeddedMarkovChainMatrix.
      match eqi currState1 0 with true
      then
        1
      else match eqi currState1 2 with true
      then
        1
      else
        let param9 =
          get
            (let target87 = embeddedQMatrix4 in
             match target87 with EmbeddedMarkovChainMatrix1 x142
             then
               x142.transitionProbs
             else
               (print
                    "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 75:18-75:49>:\nField \'transitionProbs\' not found\n[0m      let param = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1];\n")
               ; exit 1)
            (subi (addi currState1 1) 1)
        in
        let nextState3 = assume
            (Categorical param9) in
        nextState3
in
let makeStateMessage: Int -> [Float] =
  lam interaction: Int.
    match
      match geqi interaction 0 with true
      then
        leqi interaction 2
      else
        false
    with
      true
    then
      kroneckerDelta (addi interaction 1) 3
    else
      rep 3 1.
in
recursive
  let observationMessage: [Int] -> Int -> Int -> [Float] =
    lam obsRepertoire: [Int].
      lam i4: Int.
        lam max: Int.
          match leqi i4 max with true
          then
            let stateMsg = makeStateMessage (get obsRepertoire (subi i4 1))
            in
            cons1
              (get stateMsg (subi 1 1))
              (cons1
                 (get stateMsg (subi 2 1))
                 (cons1
                    (get stateMsg (subi 3 1))
                    (observationMessage obsRepertoire (addi i4 1) max)))
          else
            ""
in
recursive
  let postorderTraverse: TreeLabeled -> Matrix Float -> [[Int]] -> Int -> MsgTree =
    lam tree: TreeLabeled.
      lam qMatrix: Matrix Float.
        lam interactions: [[Int]].
          lam nhosts: Int.
            match
              match tree with Leaf _
              then
                true
              else
                false
            with
              true
            then
              let outmsg =
                mtxCreate
                  nhosts
                  3
                  (observationMessage
                     (get
                        interactions
                        (subi
                           (let target2 = tree in
                            match target2 with Node x10
                            then
                              x10.label
                            else match target2 with Leaf x11
                            then
                              x11.label
                            else
                              (print
                                   "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 9:70-9:80>:\nField \'label\' not found\n[0m    let outmsg = mtxCreate(nhosts, 3, observationMessage(interactions[[31mtree.label[0m[0m], 1, nhosts));\n")
                              ; exit 1)
                           1))
                     1
                     nhosts)
              in
              let leafInts =
                get
                  interactions
                  (subi
                     (let target1 = tree in
                      match target1 with Node x8
                      then
                        x8.label
                      else match target1 with Leaf x9
                      then
                        x9.label
                      else
                        (print
                             "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 10:32-10:42>:\nField \'label\' not found\n[0m    let leafInts = interactions[[31mtree.label[0m[0m];\n")
                        ; exit 1)
                     1)
              in
              MsgLeaf
                { age = 0.,
                  label =
                    let target = tree in
                    match target with Node x6
                    then
                      x6.label
                    else match target with Leaf x7
                    then
                      x7.label
                    else
                      (print
                           "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 13:14-13:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n")
                      ; exit 1,
                  outMsg =
                    mtxCreate nhosts 3 (observationMessage leafInts 1 nhosts),
                  interactions = leafInts }
            else
              let left =
                postorderTraverse
                  (let target12 = tree in
                   match target12 with Node x29
                   then
                     x29.left
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 19:31-19:40>:\nField \'left\' not found\n[0m  let left = postorderTraverse([31mtree.left[0m[0m, qMatrix, interactions, nhosts);\n")
                     ; exit 1)
                  qMatrix
                  interactions
                  nhosts
              in
              let right =
                postorderTraverse
                  (let target11 = tree in
                   match target11 with Node x28
                   then
                     x28.right
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 20:32-20:42>:\nField \'right\' not found\n[0m  let right = postorderTraverse([31mtree.right[0m[0m, qMatrix, interactions, nhosts);\n")
                     ; exit 1)
                  qMatrix
                  interactions
                  nhosts
              in
              let leftKernel =
                mtxExp
                  (mtxSclrMul
                     (subf
                        (let target9 = tree in
                         match target9 with Node x24
                         then
                           x24.age
                         else match target9 with Leaf x25
                         then
                           x25.age
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:37-23:45>:\nField \'age\' not found\n[0m  let leftKernel = mtxExp(mtxSclrMul([31mtree.age[0m[0m-left.age, qMatrix));\n")
                           ; exit 1)
                        (let target10 = left in
                         match target10 with MsgNode x26
                         then
                           x26.age
                         else match target10 with MsgLeaf x27
                         then
                           x27.age
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:46-23:54>:\nField \'age\' not found\n[0m  let leftKernel = mtxExp(mtxSclrMul(tree.age-[31mleft.age[0m[0m, qMatrix));\n")
                           ; exit 1))
                     qMatrix)
              in
              let rightKernel =
                mtxExp
                  (mtxSclrMul
                     (subf
                        (let target7 = tree in
                         match target7 with Node x20
                         then
                           x20.age
                         else match target7 with Leaf x21
                         then
                           x21.age
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:38-24:46>:\nField \'age\' not found\n[0m  let rightKernel = mtxExp(mtxSclrMul([31mtree.age[0m[0m-right.age, qMatrix));\n")
                           ; exit 1)
                        (let target8 = right in
                         match target8 with MsgNode x22
                         then
                           x22.age
                         else match target8 with MsgLeaf x23
                         then
                           x23.age
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:47-24:56>:\nField \'age\' not found\n[0m  let rightKernel = mtxExp(mtxSclrMul(tree.age-[31mright.age[0m[0m, qMatrix));\n")
                           ; exit 1))
                     qMatrix)
              in
              let leftBackwardKernel = mtxTrans leftKernel in
              let rightBackwardKernel = mtxTrans rightKernel in
              let leftInMsg =
                mtxMul
                  (let target6 = left in
                   match target6 with MsgNode x18
                   then
                     x18.outMsg
                   else match target6 with MsgLeaf x19
                   then
                     x19.outMsg
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 30:25-30:36>:\nField \'outMsg\' not found\n[0m  let leftInMsg = mtxMul([31mleft.outMsg[0m[0m, leftBackwardKernel);\n")
                     ; exit 1)
                  leftBackwardKernel
              in
              let rightInMsg =
                mtxMul
                  (let target5 = right in
                   match target5 with MsgNode x16
                   then
                     x16.outMsg
                   else match target5 with MsgLeaf x17
                   then
                     x17.outMsg
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 31:26-31:38>:\nField \'outMsg\' not found\n[0m  let rightInMsg = mtxMul([31mright.outMsg[0m[0m, rightBackwardKernel);\n")
                     ; exit 1)
                  rightBackwardKernel
              in
              let outMsg = mtxElemMul leftInMsg rightInMsg in
              MsgNode
                { age =
                    let target3 = tree in
                    match target3 with Node x12
                    then
                      x12.age
                    else match target3 with Leaf x13
                    then
                      x13.age
                    else
                      (print
                           "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 36:10-36:18>:\nField \'age\' not found\n[0m    age = [31mtree.age[0m[0m, label = tree.label,\n")
                      ; exit 1,
                  left = left,
                  right = right,
                  label =
                    let target4 = tree in
                    match target4 with Node x14
                    then
                      x14.label
                    else match target4 with Leaf x15
                    then
                      x15.label
                    else
                      (print
                           "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 36:28-36:38>:\nField \'label\' not found\n[0m    age = tree.age, label = [31mtree.label[0m[0m,\n")
                      ; exit 1,
                  outMsg = outMsg,
                  leftInMsg = leftInMsg,
                  rightInMsg = rightInMsg,
                  leftKernel = leftKernel,
                  rightKernel = rightKernel }
in
let categoricalLogPdf: Int -> [Float] -> Float =
  lam x141: Int.
    lam params: [Float].
      match
        match geqi x141 0 with true
        then
          lti x141 (length1 params)
        else
          false
      with
        true
      then
        log1 (get params (subi (addi x141 1) 1))
      else
        log1 0.
in
let mtx3ToSeq: Matrix Float -> Int -> [Float] =
  lam mtx: Matrix Float.
    lam i13: Int.
      let p11 = mtxGet i13 1 mtx in
      let p2 = mtxGet i13 2 mtx in
      let p3 = mtxGet i13 3 mtx in
      let s5 = addf (addf p11 p2) p3 in
      [ divf p11 s5,
        divf p2 s5,
        divf p3 s5 ]
in
let anon18: [Int] -> Matrix Float -> Float -> Int -> Float =
  lam x139.
    lam samplingProb2.
      lam acc9: Float.
        lam i12: Int.
          let x140: Float =
            let param8 = mtx3ToSeq samplingProb2 i12 in
            addf acc9 (categoricalLogPdf (get x139 (subi i12 1)) param8)
          in
          x140
in
let anon19: Int -> Int -> Int = lam start9.
    lam idx4.
      addi idx4 start9
in
let getRepertoireDebt: [Int] -> Matrix Float -> Int -> Float =
  lam x138: [Int].
    lam samplingProb1: Matrix Float.
      lam nhosts10: Int.
        fold
          (anon18 x138 samplingProb1)
          0.
          (let start8 = 1 in
           let end5 = nhosts10 in
           create1 (addi (subi end5 start8) 1) (anon19 start8))
in
let anon20: Int -> Int -> Int =
  lam acc8: Int.
    lam h2: Int.
      let x137: Int =
        match eqi h2 2 with true
        then
          addi acc8 1
        else
          acc8
      in
      x137
in
recursive
  let ifCont =
    lam currRep.
      lam eventSeq.
        lam eventIndex.
          lam nEvents.
            lam nhosts1.
              lam event.
                lam #var"1": ().
                  let newRep = updateRepertoire currRep event nhosts1 in
                  allTimesValidBranch newRep eventSeq (addi eventIndex 1) nEvents nhosts1
  let allTimesValidBranch: [Int] -> [Event] -> Int -> Int -> Int -> Bool =
    lam currRep1: [Int].
      lam eventSeq1: [Event].
        lam eventIndex1: Int.
          lam nEvents1: Int.
            lam nhosts2: Int.
              match gti eventIndex1 nEvents1 with true
              then
                true
              else
                let event1 = get eventSeq1 (subi eventIndex1 1) in
                match
                  eqi
                    (let target13 = event1 in
                     match target13 with Event1 x30
                     then
                       x30.fromState
                     else
                       (print
                            "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 146:7-146:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n")
                       ; exit 1)
                    2
                with
                  true
                then
                  let n2s1 = fold anon20 0 currRep1 in
                  match eqi n2s1 1 with true
                  then
                    false
                  else
                    ifCont currRep1 eventSeq1 eventIndex1 nEvents1 nhosts2 event1 {}
                else
                  ifCont currRep1 eventSeq1 eventIndex1 nEvents1 nhosts2 event1 {}
in
let anon21: Int -> Bool =
  lam i11: Int.
    let x136: Bool =
      match eqi i11 2 with true
      then
        true
      else
        eqi i11 1
    in
    x136
in
let anon22: Int -> Bool = lam i10: Int.
    let x135: Bool = eqi i10 2 in
    x135
in
let getGainRate: [Int] -> Int -> ModelParams -> Float =
  lam repertoire1: [Int].
    lam hostIndex3: Int.
      lam modelParams13: ModelParams.
        let fromState5 = get repertoire1 (subi hostIndex3 1) in
        let toState3 = addi fromState5 1 in
        let baseRate1 =
          mtxGet
            (addi fromState5 1)
            (addi toState3 1)
            (let target85 =
               let target86 = modelParams13 in
               match target86 with ModelParams1 x134
               then
                 x134.embeddedQMatrix
               else
                 (print
                      "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n")
                 ; exit 1
             in
             match target85 with EmbeddedMarkovChainMatrix1 x133
             then
               x133.mat
             else
               (print
                    "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n")
               ; exit 1)
        in
        match eqi fromState5 0 with true
        then
          let currentHosts = whichTrue (sapply repertoire1 anon21) in
          let dist =
            mtxMean
              (mtxRowCols
                 (let target81 = modelParams13 in
                  match target81 with ModelParams1 x129
                  then
                    x129.hostMetric
                  else
                    (print
                         "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n")
                    ; exit 1)
                 hostIndex3
                 currentHosts)
          in
          mulf
            baseRate1
            (pow
               (divf
                  dist
                  (let target79 = modelParams13 in
                   match target79 with ModelParams1 x127
                   then
                     x127.meanDist
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n")
                     ; exit 1))
               (negf
                  (let target80 = modelParams13 in
                   match target80 with ModelParams1 x128
                   then
                     x128.beta
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n")
                     ; exit 1)))
        else
          let currentHosts1 = whichTrue (sapply repertoire1 anon22) in
          let dist1 =
            mtxMean
              (mtxRowCols
                 (let target84 = modelParams13 in
                  match target84 with ModelParams1 x132
                  then
                    x132.hostMetric
                  else
                    (print
                         "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n")
                    ; exit 1)
                 hostIndex3
                 currentHosts1)
          in
          mulf
            baseRate1
            (pow
               (divf
                  dist1
                  (let target82 = modelParams13 in
                   match target82 with ModelParams1 x130
                   then
                     x130.meanDist
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n")
                     ; exit 1))
               (negf
                  (let target83 = modelParams13 in
                   match target83 with ModelParams1 x131
                   then
                     x131.beta
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n")
                     ; exit 1)))
in
let anon23: [Int] -> ModelParams -> Float -> Int -> Float =
  lam currRep6.
    lam modelParams12.
      lam acc7: Float.
        lam i9: Int.
          let x126: Float =
            let fromState4 = get currRep6 (subi i9 1) in
            match eqi fromState4 2 with true
            then
              acc7
            else
              addf acc7 (getGainRate currRep6 i9 modelParams12)
          in
          x126
in
let anon24: Int -> Int -> Int = lam start7.
    lam idx3.
      addi idx3 start7
in
let getLossRate: [Int] -> Int -> ModelParams -> Float =
  lam repertoire: [Int].
    lam hostIndex2: Int.
      lam modelParams11: ModelParams.
        let fromState3 = get repertoire (subi hostIndex2 1) in
        match
          match eqi fromState3 2 with true
          then
            eqi (n2s repertoire) 1
          else
            false
        with
          true
        then
          0.
        else
          let toState2 = subi fromState3 1 in
          let baseRate =
            mtxGet
              (addi fromState3 1)
              (addi toState2 1)
              (let target77 =
                 let target78 = modelParams11 in
                 match target78 with ModelParams1 x125
                 then
                   x125.embeddedQMatrix
                 else
                   (print
                        "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n")
                   ; exit 1
               in
               match target77 with EmbeddedMarkovChainMatrix1 x124
               then
                 x124.mat
               else
                 (print
                      "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n")
                 ; exit 1)
          in
          baseRate
in
let anon25: [Int] -> ModelParams -> Float -> Int -> Float =
  lam currRep5.
    lam modelParams10.
      lam acc6: Float.
        lam i8: Int.
          let x123: Float =
            let fromState2 = get currRep5 (subi i8 1) in
            match eqi fromState2 0 with true
            then
              acc6
            else
              addf acc6 (getLossRate currRep5 i8 modelParams10)
          in
          x123
in
let anon26: Int -> Int -> Int = lam start6.
    lam idx2.
      addi idx2 start6
in
let getTotalRate: [Int] -> ModelParams -> Int -> Float =
  lam currRep4: [Int].
    lam modelParams9: ModelParams.
      lam nhosts9: Int.
        let gainRates =
          fold
            (anon23 currRep4 modelParams9)
            0.
            (let start5 = 1 in
             let end4 = nhosts9 in
             create1 (addi (subi end4 start5) 1) (anon24 start5))
        in
        let lossRates =
          fold
            (anon25 currRep4 modelParams9)
            0.
            (let start4 = 1 in
             let end3 = nhosts9 in
             create1 (addi (subi end3 start4) 1) (anon26 start4))
        in
        addf gainRates lossRates
in
let getRate: [Int] -> Event -> ModelParams -> Float =
  lam currRep3: [Int].
    lam nextEvent2: Event.
      lam modelParams8: ModelParams.
        let hostIndex1 =
          let target76 = nextEvent2 in
          match target76 with Event1 x122
          then
            x122.host
          else
            (print
                 "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n")
            ; exit 1
        in
        match
          gti
            (let target74 = nextEvent2 in
             match target74 with Event1 x120
             then
               x120.fromState
             else
               (print
                    "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n")
               ; exit 1)
            (let target75 = nextEvent2 in
             match target75 with Event1 x121
             then
               x121.toState
             else
               (print
                    "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n")
               ; exit 1)
        with
          true
        then
          getLossRate currRep3 hostIndex1 modelParams8
        else
          getGainRate currRep3 hostIndex1 modelParams8
in
recursive
  let fullModelWeight: Int -> [Int] -> [Int] -> Float -> Float -> [Event] -> Int -> Int -> ModelParams -> Float =
    lam nextIndex: Int.
      lam currRep2: [Int].
        lam finalRep: [Int].
          lam currAge: Float.
            lam finalAge: Float.
              lam eventSeq2: [Event].
                lam nEvents2: Int.
                  lam nhosts3: Int.
                    lam modelParams: ModelParams.
                      match gti nextIndex nEvents2 with true
                      then
                        let timePassed = subf currAge finalAge in
                        let totalLeavingRate = getTotalRate currRep2 modelParams nhosts3
                        in
                        mulf (negf timePassed) totalLeavingRate
                      else
                        let nextEvent = get eventSeq2 (subi nextIndex 1) in
                        let newAge =
                          let target14 = nextEvent in
                          match target14 with Event1 x31
                          then
                            x31.eventTime
                          else
                            (print
                                 "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n")
                            ; exit 1
                        in
                        let totalLeavingRate1 = getTotalRate currRep2 modelParams nhosts3
                        in
                        let thisRate = getRate currRep2 nextEvent modelParams in
                        let timePassed1 = subf currAge newAge in
                        let thisWeight =
                          subf
                            (log1 (divf thisRate totalLeavingRate1))
                            (mulf timePassed1 totalLeavingRate1)
                        in
                        let newRep1 = updateRepertoire currRep2 nextEvent nhosts3 in
                        addf
                          thisWeight
                          (fullModelWeight
                             (addi nextIndex 1)
                             newRep1
                             finalRep
                             newAge
                             finalAge
                             eventSeq2
                             nEvents2
                             nhosts3
                             modelParams)
in
let newParamFun =
  lam alpha2.
    lam epsilon1.
      lam a35: Float.
        let x119: Float =
          match gtf a35 epsilon1 with true
          then
            match ltf a35 (subf 1. epsilon1) with true
            then
              mulf a35 alpha2
            else
              mulf (subf a35 epsilon1) alpha2
          else
            mulf (addf a35 epsilon1) alpha2
        in
        x119
in
let simplexMove: [Float] -> Float -> Float -> Dist([Float]) =
  lam x118: [Float].
    lam alpha1: Float.
      lam epsilon: Float.
        let newParams = sapply x118 (newParamFun alpha1 epsilon) in
        Dirichlet newParams
in
let scaleMove: Float -> Float -> Dist(Float) =
  lam x117: Float.
    lam lambda6: Float.
      Reciprocal
        (mulf x117 (exp1 (divf (negf lambda6) 2.)))
        (mulf x117 (exp1 (divf lambda6 2.)))
in
let anon27: Int -> Int -> Int = lam start3.
    lam idx1.
      addi idx1 start3
in
let anon28: Int -> [Float] -> Float -> Float -> Int -> Float =
  lam x115.
    lam param7.
      lam currProb1.
        lam nextProb1.
          lam i7: Int.
            let x116: Float =
              match eqi i7 x115 with true
              then
                nextProb1
              else
                divf
                  (mulf (get param7 (subi (addi i7 1) 1)) (subf 1. nextProb1))
                  (subf 1. currProb1)
            in
            x116
in
let categoricalShiftKernel: Int -> [Float] -> Float -> Float -> Dist(Int) =
  lam x114: Int.
    lam param6: [Float].
      lam lambda5: Float.
        lam errMargin1: Float.
          let currProb = get param6 (subi (addi x114 1) 1) in
          match ltf currProb (subf 1. errMargin1) with true
          then
            let nextProb = mulf currProb (subf 1. lambda5) in
            let newParam =
              sapply
                (let start2 = 1 in
                 let end2 = length1 param6 in
                 create1 (addi (subi end2 start2) 1) (anon27 start2))
                (anon28 x114 param6 currProb nextProb)
            in
            Categorical newParam
          else
            Categorical param6
in
let rbLambdaMove: [Float] -> Dist([Float]) =
  lam x113: [Float].
    let _EPSILON = 0.001 in
    let alpha = 25. in
    simplexMove x113 alpha _EPSILON
in
let rbBetaMove: Float -> Dist(Float) =
  lam x112: Float.
    let lambda4 = 1. in
    scaleMove x112 lambda4
in
let rbMuMove: Float -> Dist(Float) =
  lam x111: Float.
    let lambda3 = 0.2 in
    scaleMove x111 lambda3
in
let categoricalMove: Int -> [Float] -> Dist(Int) =
  lam x110: Int.
    lam param5: [Float].
      let lambda2 = 0.9 in
      let errMargin = 1e-06 in
      categoricalShiftKernel x110 param5 lambda2 errMargin
in
recursive
  let hostIndepLikelihood: Int -> Int -> Int -> Float -> Float -> [Event] -> EmbeddedMarkovChainMatrix -> Float =
    lam nextIndex1: Int.
      lam currState: Int.
        lam finalState: Int.
          lam currAge1: Float.
            lam finalAge1: Float.
              lam eventSeq3: [Event].
                lam embeddedQMatrix: EmbeddedMarkovChainMatrix.
                  match gti nextIndex1 (length1 eventSeq3) with true
                  then
                    let timePassed2 = subf currAge1 finalAge1 in
                    let outRate =
                      get
                        (let target15 = embeddedQMatrix in
                         match target15 with EmbeddedMarkovChainMatrix1 x32
                         then
                           x32.totalRates
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n")
                           ; exit 1)
                        (subi (addi currState 1) 1)
                    in
                    mulf (negf timePassed2) outRate
                  else
                    let nextEvent1 = get eventSeq3 (subi nextIndex1 1) in
                    let nextState =
                      let target19 = nextEvent1 in
                      match target19 with Event1 x36
                      then
                        x36.toState
                      else
                        (print
                             "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n")
                        ; exit 1
                    in
                    let nextAge =
                      let target18 = nextEvent1 in
                      match target18 with Event1 x35
                      then
                        x35.eventTime
                      else
                        (print
                             "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n")
                        ; exit 1
                    in
                    let timePassed3 = subf currAge1 nextAge in
                    let outRate1 =
                      get
                        (let target17 = embeddedQMatrix in
                         match target17 with EmbeddedMarkovChainMatrix1 x34
                         then
                           x34.totalRates
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n")
                           ; exit 1)
                        (subi (addi currState 1) 1)
                    in
                    let transProb =
                      get
                        (get
                           (let target16 = embeddedQMatrix in
                            match target16 with EmbeddedMarkovChainMatrix1 x33
                            then
                              x33.transitionProbs
                            else
                              (print
                                   "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n")
                              ; exit 1)
                           (subi (addi currState 1) 1))
                        (subi (addi nextState 1) 1)
                    in
                    addf
                      (subf (log1 transProb) (mulf timePassed3 outRate1))
                      (hostIndepLikelihood
                         (addi nextIndex1 1)
                         nextState
                         finalState
                         nextAge
                         finalAge1
                         eventSeq3
                         embeddedQMatrix)
in
let anon29: [Int] -> [Int] -> Float -> Float -> [[Event]] -> ModelParams -> Float -> Int -> Float =
  lam fromRep2.
    lam toRep2.
      lam fromAge2.
        lam toAge2.
          lam eventSeqs2.
            lam modelParams7.
              lam acc5: Float.
                lam h1: Int.
                  let x108: Float =
                    let eventSeq4 = get eventSeqs2 (subi h1 1) in
                    let fromState1 = get fromRep2 (subi h1 1) in
                    let toState1 = get toRep2 (subi h1 1) in
                    addf
                      acc5
                      (hostIndepLikelihood
                         1
                         fromState1
                         toState1
                         fromAge2
                         toAge2
                         eventSeq4
                         (let target73 = modelParams7 in
                          match target73 with ModelParams1 x109
                          then
                            x109.embeddedQMatrix
                          else
                            (print
                                 "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n")
                            ; exit 1))
                  in
                  x108
in
let anon30: Int -> Int -> Int = lam start1.
    lam idx.
      addi idx start1
in
let independenceLikelihood: [Int] -> [Int] -> Float -> Float -> [[Event]] -> ModelParams -> Float =
  lam fromRep1: [Int].
    lam toRep1: [Int].
      lam fromAge1: Float.
        lam toAge1: Float.
          lam eventSeqs1: [[Event]].
            lam modelParams6: ModelParams.
              let unconditional1 =
                fold
                  (anon29 fromRep1 toRep1 fromAge1 toAge1 eventSeqs1 modelParams6)
                  0.
                  (let start = 1 in
                   let end1 = length1 eventSeqs1 in
                   create1 (addi (subi end1 start) 1) (anon30 start))
              in
              unconditional1
in
let anon31: Float -> Float -> Float =
  lam acc4: Float.
    lam val: Float.
      let x107: Float = addf acc4 val in
      x107
in
let anon32: Matrix Float -> Int -> Int -> Float =
  lam kernel1.
    lam fromState: Int.
      lam toState: Int.
        let x106: Float = log1 (mtxGet (addi fromState 1) (addi toState 1) kernel1)
        in
        x106
in
let independenceLikelihoodEndCond: [Int] -> [Int] -> Float -> Float -> [[Event]] -> ModelParams -> Matrix Float -> Float =
  lam fromRep: [Int].
    lam toRep: [Int].
      lam fromAge: Float.
        lam toAge: Float.
          lam eventSeqs: [[Event]].
            lam modelParams5: ModelParams.
              lam kernel: Matrix Float.
                let unconditional =
                  independenceLikelihood fromRep toRep fromAge toAge eventSeqs modelParams5
                in
                let logTotalTransProb = fold anon31 0. (zipWith1 (anon32 kernel) fromRep toRep)
                in
                let conditional = subf unconditional logTotalTransProb in
                conditional
in
type ReturnType in
con ReturnType1: {mu: Float, beta: Float, tree: HistoryTree, lambda: [Float]} -> ReturnType
in
let compAge: Event -> Event -> Int =
  lam left2: Event.
    lam right2: Event.
      match
        isNaN1
          (let target69 = right2 in
           match target69 with Event1 x102
           then
             x102.eventTime
           else
             (print
                  "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 282:12-282:27>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mright.eventTime[0m[0m)) {\n")
             ; exit 1)
      with
        true
      then
        negi 1
      else match
        isNaN1
          (let target70 = left2 in
           match target70 with Event1 x103
           then
             x103.eventTime
           else
             (print
                  "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 285:12-285:26>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mleft.eventTime[0m[0m)) {\n")
             ; exit 1)
      with
        true
      then
        1
      else match
        geqf
          (let target71 = right2 in
           match target71 with Event1 x104
           then
             x104.eventTime
           else
             (print
                  "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 288:6-288:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n")
             ; exit 1)
          (let target72 = left2 in
           match target72 with Event1 x105
           then
             x105.eventTime
           else
             (print
                  "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 288:25-288:39>:\nField \'eventTime\' not found\n[0m  if (right.eventTime >= [31mleft.eventTime[0m[0m) {\n")
             ; exit 1)
      with
        true
      then
        1
      else
        negi 1
in
let sampleTruncatedExponential: Float -> Float -> Float =
  lam rate: Float.
    lam maxT: Float.
      let uMin = exp1 (mulf (negf rate) maxT) in
      let u_ = assume
          (Uniform 0. 1.) in
      let u = addf uMin (mulf u_ (subf 1. uMin)) in
      let expSample = divf (negf (log1 u)) rate in
      expSample
in
let anon33 =
  lam l1: Int.
    lam r2: Int.
      match eqi l1 r2 with true
      then
        false
      else
        true
in
recursive
  let sampleHostHistory: Int -> Int -> Float -> Float -> Int -> EmbeddedMarkovChainMatrix -> Int -> HostBranchSample =
    lam startState: Int.
      lam finalState1: Int.
        lam startAge: Float.
          lam finalAge2: Float.
            lam host: Int.
              lam embeddedQMatrix1: EmbeddedMarkovChainMatrix.
                lam stepIndex: Int.
                  let totalRate =
                    get
                      (let target26 = embeddedQMatrix1 in
                       match target26 with EmbeddedMarkovChainMatrix1 x43
                       then
                         x43.totalRates
                       else
                         (print
                              "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 349:18-349:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n")
                         ; exit 1)
                      (subi (addi startState 1) 1)
                  in
                  match
                    match anon33 startState finalState1 with true
                    then
                      eqi stepIndex 1
                    else
                      false
                  with
                    true
                  then
                    let t1 =
                      sampleTruncatedExponential totalRate (subf startAge finalAge2)
                    in
                    let eventTime = subf startAge t1 in
                    let nextState1 = sampleNextEvent startState embeddedQMatrix1 in
                    let param =
                      get
                        (let target22 = embeddedQMatrix1 in
                         match target22 with EmbeddedMarkovChainMatrix1 x39
                         then
                           x39.transitionProbs
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 358:16-358:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[startState + 1];\n")
                           ; exit 1)
                        (subi (addi startState 1) 1)
                    in
                    let restOfHistory =
                      sampleHostHistory
                        nextState1
                        finalState1
                        eventTime
                        finalAge2
                        host
                        embeddedQMatrix1
                        (addi stepIndex 1)
                    in
                    HostBranchSample1
                      { history =
                          cons1
                            (Event1
                               { eventTime = eventTime,
                                 fromState = startState,
                                 toState = nextState1,
                                 host = host })
                            (let target20 = restOfHistory in
                             match target20 with HostBranchSample1 x37
                             then
                               x37.history
                             else
                               (print
                                    "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 364:8-364:29>:\nField \'history\' not found\n[0m        [31mrestOfHistory.history[0m\n")
                               ; exit 1),
                        success =
                          let target21 = restOfHistory in
                          match target21 with HostBranchSample1 x38
                          then
                            x38.success
                          else
                            (print
                                 "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 366:16-366:37>:\nField \'success\' not found\n[0m      success = [31mrestOfHistory.success[0m\n")
                            ; exit 1 }
                  else
                    let t2 = assume
                        (Exponential totalRate)
                    in
                    match ltf (subf startAge t2) finalAge2 with true
                    then
                      match eqi startState finalState1 with true
                      then
                        HostBranchSample1
                          { history = "", success = true }
                      else
                        HostBranchSample1
                          { history = "", success = false }
                    else
                      let nextState2 = sampleNextEvent startState embeddedQMatrix1 in
                      let param1 =
                        get
                          (let target25 = embeddedQMatrix1 in
                           match target25 with EmbeddedMarkovChainMatrix1 x42
                           then
                             x42.transitionProbs
                           else
                             (print
                                  "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 390:18-390:49>:\nField \'transitionProbs\' not found\n[0m      let param = [31membeddedQMatrix.transitionProbs[0m[0m[startState + 1];\n")
                             ; exit 1)
                          (subi (addi startState 1) 1)
                      in
                      let eventTime1 = subf startAge t2 in
                      let restOfHistory1 =
                        sampleHostHistory
                          nextState2
                          finalState1
                          eventTime1
                          finalAge2
                          host
                          embeddedQMatrix1
                          (addi stepIndex 1)
                      in
                      HostBranchSample1
                        { history =
                            cons1
                              (Event1
                                 { eventTime = eventTime1,
                                   fromState = startState,
                                   toState = nextState2,
                                   host = host })
                              (let target23 = restOfHistory1 in
                               match target23 with HostBranchSample1 x40
                               then
                                 x40.history
                               else
                                 (print
                                      "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 399:10-399:31>:\nField \'history\' not found\n[0m          [31mrestOfHistory.history[0m\n")
                                 ; exit 1),
                          success =
                            let target24 = restOfHistory1 in
                            match target24 with HostBranchSample1 x41
                            then
                              x41.success
                            else
                              (print
                                   "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 401:18-401:39>:\nField \'success\' not found\n[0m        success = [31mrestOfHistory.success[0m\n")
                              ; exit 1 }
in
recursive
  let sampleUnorderedBranch: [Int] -> [Int] -> Float -> Float -> Int -> Int -> EmbeddedMarkovChainMatrix -> Int -> BranchSample =
    lam startRep: [Int].
      lam finalRep1: [Int].
        lam startAge1: Float.
          lam finalAge3: Float.
            lam hostIndex: Int.
              lam nhosts4: Int.
                lam embeddedQMatrix2: EmbeddedMarkovChainMatrix.
                  lam rejectionDepth: Int.
                    let _MAX_REJECTION_DEPTH_HOST = 100 in
                    match leqi hostIndex nhosts4 with true
                    then
                      let hostHistory =
                        sampleHostHistory
                          (get startRep (subi hostIndex 1))
                          (get finalRep1 (subi hostIndex 1))
                          startAge1
                          finalAge3
                          hostIndex
                          embeddedQMatrix2
                          1
                      in
                      match
                        let target27 = hostHistory in
                        match target27 with HostBranchSample1 x44
                        then
                          x44.success
                        else
                          (print
                               "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 311:7-311:26>:\nField \'success\' not found\n[0m    if [31mhostHistory.success[0m[0m {\n")
                          ; exit 1
                      with
                        true
                      then
                        let otherHostHistories =
                          sampleUnorderedBranch
                            startRep
                            finalRep1
                            startAge1
                            finalAge3
                            (addi hostIndex 1)
                            nhosts4
                            embeddedQMatrix2
                            0
                        in
                        BranchSample1
                          { history =
                              cons1
                                (let target28 = hostHistory in
                                 match target28 with HostBranchSample1 x45
                                 then
                                   x45.history
                                 else
                                   (print
                                        "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 316:23-316:42>:\nField \'history\' not found\n[0m        history = cons([31mhostHistory.history[0m[0m, otherHostHistories.history),\n")
                                   ; exit 1)
                                (let target29 = otherHostHistories in
                                 match target29 with BranchSample1 x46
                                 then
                                   x46.history
                                 else
                                   (print
                                        "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 316:44-316:70>:\nField \'history\' not found\n[0m        history = cons(hostHistory.history, [31motherHostHistories.history[0m[0m),\n")
                                   ; exit 1),
                            success =
                              let target30 = otherHostHistories in
                              match target30 with BranchSample1 x47
                              then
                                x47.success
                              else
                                (print
                                     "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 317:18-317:44>:\nField \'success\' not found\n[0m        success = [31motherHostHistories.success[0m\n")
                                ; exit 1 }
                      else match leqi rejectionDepth _MAX_REJECTION_DEPTH_HOST with true
                      then
                        sampleUnorderedBranch
                          startRep
                          finalRep1
                          startAge1
                          finalAge3
                          hostIndex
                          nhosts4
                          embeddedQMatrix2
                          (addi rejectionDepth 1)
                      else
                        BranchSample1
                          { history = "", success = false }
                    else
                      BranchSample1
                        { history = "", success = true }
in
recursive
  let ifCont1 =
    lam startRep1.
      lam finalRep2.
        lam startAge2.
          lam finalAge4.
            lam nhosts5.
              lam modelParams1.
                lam branchKernel.
                  lam rejectionDepth1.
                    lam #var"2": ().
                      sampleBranch
                        startRep1
                        finalRep2
                        startAge2
                        finalAge4
                        nhosts5
                        modelParams1
                        branchKernel
                        (addi rejectionDepth1 1)
  let sampleBranch: [Int] -> [Int] -> Float -> Float -> Int -> ModelParams -> Matrix Float -> Int -> CorrectedBranchSample =
    lam startRep2: [Int].
      lam finalRep3: [Int].
        lam startAge3: Float.
          lam finalAge5: Float.
            lam nhosts6: Int.
              lam modelParams2: ModelParams.
                lam branchKernel1: Matrix Float.
                  lam rejectionDepth2: Int.
                    let _MAX_REJECTION_DEPTH_BRANCH = 100 in
                    match leqi rejectionDepth2 _MAX_REJECTION_DEPTH_BRANCH with true
                    then
                      let unorderedBranch =
                        sampleUnorderedBranch
                          startRep2
                          finalRep3
                          startAge3
                          finalAge5
                          1
                          nhosts6
                          (let target34 = modelParams2 in
                           match target34 with ModelParams1 x51
                           then
                             x51.embeddedQMatrix
                           else
                             (print
                                  "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 227:57-227:84>:\nField \'embeddedQMatrix\' not found\n[0m      startRep, finalRep, startAge, finalAge, 1, nhosts, [31mmodelParams.embeddedQMatrix[0m[0m, 1\n")
                             ; exit 1)
                          1
                      in
                      match
                        let target31 = unorderedBranch in
                        match target31 with BranchSample1 x48
                        then
                          x48.success
                        else
                          (print
                               "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 229:7-229:30>:\nField \'success\' not found\n[0m    if [31munorderedBranch.success[0m[0m {\n")
                          ; exit 1
                      with
                        true
                      then
                        let allHostEvents =
                          paste0
                            (let target33 = unorderedBranch in
                             match target33 with BranchSample1 x50
                             then
                               x50.history
                             else
                               (print
                                    "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 233:33-233:56>:\nField \'history\' not found\n[0m      let allHostEvents = paste0([31munorderedBranch.history[0m[0m);\n")
                               ; exit 1)
                        in
                        let orderedEvents = qSort compAge allHostEvents in
                        let nEvents3 = length1 orderedEvents in
                        match
                          allTimesValidBranch startRep2 orderedEvents 1 nEvents3 nhosts6
                        with
                          true
                        then
                          let logDebt =
                            independenceLikelihoodEndCond
                              startRep2
                              finalRep3
                              startAge3
                              finalAge5
                              (let target32 = unorderedBranch in
                               match target32 with BranchSample1 x49
                               then
                                 x49.history
                               else
                                 (print
                                      "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 243:50-243:73>:\nField \'history\' not found\n[0m          startRep, finalRep, startAge, finalAge, [31munorderedBranch.history[0m[0m, modelParams, branchKernel\n")
                                 ; exit 1)
                              modelParams2
                              branchKernel1
                          in
                          let logExcess =
                            fullModelWeight
                              1
                              startRep2
                              finalRep3
                              startAge3
                              finalAge5
                              orderedEvents
                              nEvents3
                              nhosts6
                              modelParams2
                          in
                          CorrectedBranchSample1
                            { history = orderedEvents,
                              success = true,
                              logDebt = logDebt,
                              logExcess = logExcess }
                        else
                          ifCont1
                            startRep2
                            finalRep3
                            startAge3
                            finalAge5
                            nhosts6
                            modelParams2
                            branchKernel1
                            rejectionDepth2
                            {}
                      else
                        ifCont1
                          startRep2
                          finalRep3
                          startAge3
                          finalAge5
                          nhosts6
                          modelParams2
                          branchKernel1
                          rejectionDepth2
                          {}
                    else
                      CorrectedBranchSample1
                        { history = "",
                          success = false,
                          logDebt = negf (log1 0.),
                          logExcess = log1 0. }
in
let anon34: [Float] -> Int -> Dist(Int) = lam param4.
    lam x101.
      categoricalMove x101 param4
in
recursive
  let suggestRepAligned: Matrix Float -> Int -> Int -> [Int] =
    lam msg: Matrix Float.
      lam i5: Int.
        lam max1: Int.
          match leqi i5 max1 with true
          then
            let param2 = mtx3ToSeq msg i5 in
            let x52 = assume
                (Categorical param2) in
            cons1 x52 (suggestRepAligned msg (addi i5 1) max1)
          else
            ""
in
recursive
  let suggestRepUnaligned: Matrix Float -> Int -> Int -> [Int] =
    lam msg1: Matrix Float.
      lam i6: Int.
        lam max2: Int.
          match leqi i6 max2 with true
          then
            let param3 = mtx3ToSeq msg1 i6 in
            let x53 = assume
                (Categorical param3) in
            paste0
              [ [ x53 ],
                suggestRepUnaligned msg1 (addi i6 1) max2 ]
          else
            ""
in
recursive
  let suggestRepRS: Matrix Float -> Int -> [Int] -> Int -> [Int] =
    lam msg2: Matrix Float.
      lam max3: Int.
        lam initialRep: [Int].
          lam depth: Int.
            let _REP_REJECTION_DEPTH = 10 in
            match any1 is2 initialRep with true
            then
              initialRep
            else match lti depth _REP_REJECTION_DEPTH with true
            then
              let newRep2 = suggestRepUnaligned msg2 1 max3 in
              suggestRepRS msg2 max3 newRep2 (addi depth 1)
            else
              let foo = weight
                  (externalLog 0.) in
              initialRep
in
recursive
  let sampleTreeHistory: MsgTree -> Int -> Matrix Float -> [Int] -> Float -> ModelParams -> Matrix Float -> HistoryTree =
    lam tree1: MsgTree.
      lam nhosts7: Int.
        lam preorderMsg: Matrix Float.
          lam parentRep: [Int].
            lam parentAge: Float.
              lam modelParams3: ModelParams.
                lam branchKernel2: Matrix Float.
                  match
                    match tree1 with MsgLeaf _
                    then
                      true
                    else
                      false
                  with
                    true
                  then
                    let rep1 =
                      let target42 = tree1 in
                      match target42 with MsgLeaf x64
                      then
                        x64.interactions
                      else
                        (print
                             "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 136:14-136:31>:\nField \'interactions\' not found\n[0m    let rep = [31mtree.interactions[0m[0m;\n")
                        ; exit 1
                    in
                    let branchSample =
                      sampleBranch
                        parentRep
                        rep1
                        parentAge
                        (let target41 = tree1 in
                         match target41 with MsgNode x62
                         then
                           x62.age
                         else match target41 with MsgLeaf x63
                         then
                           x63.age
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 142:6-142:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n")
                           ; exit 1)
                        nhosts7
                        modelParams3
                        branchKernel2
                        0
                    in
                    let #var"3" =
                      match
                        let target38 = branchSample in
                        match target38 with CorrectedBranchSample1 x59
                        then
                          x59.success
                        else
                          (print
                               "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 150:7-150:27>:\nField \'success\' not found\n[0m    if [31mbranchSample.success[0m[0m {\n")
                          ; exit 1
                      with
                        true
                      then
                        let foo1 =
                          weight
                            (subf
                               (let target39 = branchSample in
                                match target39 with CorrectedBranchSample1 x60
                                then
                                  x60.logExcess
                                else
                                  (print
                                       "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 151:16-151:38>:\nField \'logExcess\' not found\n[0m      logWeight [31mbranchSample.logExcess[0m[0m - branchSample.logDebt;\n")
                                  ; exit 1)
                               (let target40 = branchSample in
                                match target40 with CorrectedBranchSample1 x61
                                then
                                  x61.logDebt
                                else
                                  (print
                                       "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 151:41-151:61>:\nField \'logDebt\' not found\n[0m      logWeight branchSample.logExcess - [31mbranchSample.logDebt[0m[0m;\n")
                                  ; exit 1))
                        in
                        {}
                      else
                        let foo2 = weight
                            (externalLog 0.)
                        in
                        {}
                    in
                    HistoryLeaf
                      { age =
                          let target35 = tree1 in
                          match target35 with MsgNode x54
                          then
                            x54.age
                          else match target35 with MsgLeaf x55
                          then
                            x55.age
                          else
                            (print
                                 "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 158:12-158:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n")
                            ; exit 1,
                        label =
                          let target36 = tree1 in
                          match target36 with MsgNode x56
                          then
                            x56.label
                          else match target36 with MsgLeaf x57
                          then
                            x57.label
                          else
                            (print
                                 "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 159:14-159:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n")
                            ; exit 1,
                        repertoire = rep1,
                        history =
                          let target37 = branchSample in
                          match target37 with CorrectedBranchSample1 x58
                          then
                            x58.history
                          else
                            (print
                                 "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 161:16-161:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n")
                            ; exit 1 }
                  else
                    let samplingProb =
                      mtxElemMul
                        (let target58 = tree1 in
                         match target58 with MsgNode x85
                         then
                           x85.outMsg
                         else match target58 with MsgLeaf x86
                         then
                           x86.outMsg
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 164:34-164:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n")
                           ; exit 1)
                        preorderMsg
                    in
                    let initRep = suggestRepAligned samplingProb 1 nhosts7 in
                    let rep2 = suggestRepRS samplingProb nhosts7 initRep 0 in
                    let nodeLogDebt = getRepertoireDebt rep2 samplingProb nhosts7
                    in
                    let branchSample1 =
                      sampleBranch
                        parentRep
                        rep2
                        parentAge
                        (let target57 = tree1 in
                         match target57 with MsgNode x83
                         then
                           x83.age
                         else match target57 with MsgLeaf x84
                         then
                           x84.age
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 174:6-174:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n")
                           ; exit 1)
                        nhosts7
                        modelParams3
                        branchKernel2
                        0
                    in
                    let #var"4" =
                      match
                        let target54 = branchSample1 in
                        match target54 with CorrectedBranchSample1 x80
                        then
                          x80.success
                        else
                          (print
                               "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 182:7-182:27>:\nField \'success\' not found\n[0m    if [31mbranchSample.success[0m[0m {\n")
                          ; exit 1
                      with
                        true
                      then
                        let foo3 =
                          weight
                            (subf
                               (subf
                                  (let target55 = branchSample1 in
                                   match target55 with CorrectedBranchSample1 x81
                                   then
                                     x81.logExcess
                                   else
                                     (print
                                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 183:16-183:38>:\nField \'logExcess\' not found\n[0m      logWeight [31mbranchSample.logExcess[0m[0m - branchSample.logDebt - nodeLogDebt;\n")
                                     ; exit 1)
                                  (let target56 = branchSample1 in
                                   match target56 with CorrectedBranchSample1 x82
                                   then
                                     x82.logDebt
                                   else
                                     (print
                                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 183:41-183:61>:\nField \'logDebt\' not found\n[0m      logWeight branchSample.logExcess - [31mbranchSample.logDebt[0m[0m - nodeLogDebt;\n")
                                     ; exit 1))
                               nodeLogDebt)
                        in
                        {}
                      else
                        let foo4 = weight
                            (externalLog 0.)
                        in
                        {}
                    in
                    let newMsg = mtxCreate nhosts7 3 (observationMessage rep2 1 nhosts7)
                    in
                    let leftMsg =
                      mtxMul
                        newMsg
                        (let target53 = tree1 in
                         match target53 with MsgNode x79
                         then
                           x79.leftKernel
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 191:33-191:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n")
                           ; exit 1)
                    in
                    let rightMsg =
                      mtxMul
                        newMsg
                        (let target52 = tree1 in
                         match target52 with MsgNode x78
                         then
                           x78.rightKernel
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 192:34-192:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n")
                           ; exit 1)
                    in
                    let left1 =
                      sampleTreeHistory
                        (let target49 = tree1 in
                         match target49 with MsgNode x74
                         then
                           x74.left
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 196:6-196:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nhosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n")
                           ; exit 1)
                        nhosts7
                        leftMsg
                        rep2
                        (let target50 = tree1 in
                         match target50 with MsgNode x75
                         then
                           x75.age
                         else match target50 with MsgLeaf x76
                         then
                           x76.age
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 196:39-196:47>:\nField \'age\' not found\n[0m      tree.left, nhosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n")
                           ; exit 1)
                        modelParams3
                        (let target51 = tree1 in
                         match target51 with MsgNode x77
                         then
                           x77.leftKernel
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 196:62-196:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nhosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n")
                           ; exit 1)
                    in
                    let right1 =
                      sampleTreeHistory
                        (let target46 = tree1 in
                         match target46 with MsgNode x70
                         then
                           x70.right
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 199:6-199:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nhosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n")
                           ; exit 1)
                        nhosts7
                        rightMsg
                        rep2
                        (let target47 = tree1 in
                         match target47 with MsgNode x71
                         then
                           x71.age
                         else match target47 with MsgLeaf x72
                         then
                           x72.age
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 199:41-199:49>:\nField \'age\' not found\n[0m      tree.right, nhosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n")
                           ; exit 1)
                        modelParams3
                        (let target48 = tree1 in
                         match target48 with MsgNode x73
                         then
                           x73.rightKernel
                         else
                           (print
                                "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 199:64-199:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nhosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n")
                           ; exit 1)
                    in
                    HistoryNode
                      { age =
                          let target43 = tree1 in
                          match target43 with MsgNode x65
                          then
                            x65.age
                          else match target43 with MsgLeaf x66
                          then
                            x66.age
                          else
                            (print
                                 "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 203:12-203:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n")
                            ; exit 1,
                        left = left1,
                        right = right1,
                        label =
                          let target44 = tree1 in
                          match target44 with MsgNode x67
                          then
                            x67.label
                          else match target44 with MsgLeaf x68
                          then
                            x68.label
                          else
                            (print
                                 "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 204:14-204:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n")
                            ; exit 1,
                        repertoire = rep2,
                        history =
                          let target45 = branchSample1 in
                          match target45 with CorrectedBranchSample1 x69
                          then
                            x69.history
                          else
                            (print
                                 "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 206:16-206:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n")
                            ; exit 1 }
in
let anon35: [Float] -> Dist([Float]) = lam lambda1.
    rbLambdaMove lambda1
in
let anon36: Float -> Dist(Float) = lam mu1.
    rbMuMove mu1 in
let anon37: Float -> Dist(Float) = lam beta1.
    rbBetaMove beta1
in
let rejectAccept: TreeLabeled -> Int -> Int -> [Int] -> [Float] -> Float -> ReturnType =
  lam symbiont_tree: TreeLabeled.
    lam ntips: Int.
      lam nhosts8: Int.
        lam interactions1: [Int].
          lam host_distances: [Float].
            lam dMean: Float.
              let lambda = assume
                  (Dirichlet [ 1., 1., 1., 1. ])
              in
              let mu = assume
                  (Exponential 10.) in
              let beta = assume
                  (Exponential 1.) in
              let r1 =
                mtxCreate
                  3
                  3
                  [ subf 0. (get lambda (subi 1 1)),
                    get lambda (subi 1 1),
                    0.,
                    get lambda (subi 2 1),
                    subf 0. (addf (get lambda (subi 2 1)) (get lambda (subi 3 1))),
                    get lambda (subi 3 1),
                    0.,
                    get lambda (subi 4 1),
                    subf 0. (get lambda (subi 4 1)) ]
              in
              let qMatrix1 = mtxSclrMul mu r1 in
              let nestedInteractions = nestSeq interactions1 ntips nhosts8 in
              let postorderTree =
                postorderTraverse symbiont_tree qMatrix1 nestedInteractions nhosts8
              in
              let rootPrior = mtxCreate nhosts8 3 (ones (muli 3 nhosts8)) in
              let rootSamplingProb =
                mtxElemMul
                  (let target68 = postorderTree in
                   match target68 with MsgNode x99
                   then
                     x99.outMsg
                   else match target68 with MsgLeaf x100
                   then
                     x100.outMsg
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 41:36-41:56>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31mpostorderTree.outMsg[0m[0m, rootPrior);\n")
                     ; exit 1)
                  rootPrior
              in
              let initRootRep = suggestRepAligned rootSamplingProb 1 nhosts8
              in
              let rootRep = suggestRepRS rootSamplingProb nhosts8 initRootRep 0
              in
              let rootLogDebt = getRepertoireDebt rootRep rootSamplingProb nhosts8
              in
              let rootLogExcess =
                negf
                  (log1
                     (subf (pow 3. (int2float nhosts8)) (pow 2. (int2float nhosts8))))
              in
              let foo5 = weight
                  (subf rootLogExcess rootLogDebt)
              in
              let newMsg1 = mtxCreate nhosts8 3 (observationMessage rootRep 1 nhosts8)
              in
              let leftMsg1 =
                mtxMul
                  newMsg1
                  (let target67 = postorderTree in
                   match target67 with MsgNode x98
                   then
                     x98.leftKernel
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 54:31-54:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n")
                     ; exit 1)
              in
              let rightMsg1 =
                mtxMul
                  newMsg1
                  (let target66 = postorderTree in
                   match target66 with MsgNode x97
                   then
                     x97.rightKernel
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 55:32-55:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n")
                     ; exit 1)
              in
              let embeddedQMatrix3 = rateMatrixToEmbeddedMarkovChain qMatrix1
              in
              let modelParams4 =
                ModelParams1
                  { beta = beta,
                    hostMetric = mtxCreate nhosts8 nhosts8 host_distances,
                    embeddedQMatrix = embeddedQMatrix3,
                    meanDist = dMean }
              in
              let rootAge =
                let target65 = postorderTree in
                match target65 with MsgNode x95
                then
                  x95.age
                else match target65 with MsgLeaf x96
                then
                  x96.age
                else
                  (print
                       "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 67:16-67:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n")
                  ; exit 1
              in
              let leftRepertoireTree =
                sampleTreeHistory
                  (let target63 = postorderTree in
                   match target63 with MsgNode x93
                   then
                     x93.left
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 69:4-69:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nhosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n")
                     ; exit 1)
                  nhosts8
                  leftMsg1
                  rootRep
                  rootAge
                  modelParams4
                  (let target64 = postorderTree in
                   match target64 with MsgNode x94
                   then
                     x94.leftKernel
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 69:72-69:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nhosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n")
                     ; exit 1)
              in
              let rightRepertoireTree =
                sampleTreeHistory
                  (let target61 = postorderTree in
                   match target61 with MsgNode x91
                   then
                     x91.right
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 72:4-72:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nhosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n")
                     ; exit 1)
                  nhosts8
                  rightMsg1
                  rootRep
                  rootAge
                  modelParams4
                  (let target62 = postorderTree in
                   match target62 with MsgNode x92
                   then
                     x92.rightKernel
                   else
                     (print
                          "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 72:74-72:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nhosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n")
                     ; exit 1)
              in
              let historyTree =
                HistoryNode
                  { age =
                      let target59 = symbiont_tree in
                      match target59 with Node x87
                      then
                        x87.age
                      else match target59 with Leaf x88
                      then
                        x88.age
                      else
                        (print
                             "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 77:10-77:27>:\nField \'age\' not found\n[0m    age = [31msymbiont_tree.age[0m[0m, label = symbiont_tree.label,\n")
                        ; exit 1,
                    left = leftRepertoireTree,
                    right = rightRepertoireTree,
                    label =
                      let target60 = symbiont_tree in
                      match target60 with Node x89
                      then
                        x89.label
                      else match target60 with Leaf x90
                      then
                        x90.label
                      else
                        (print
                             "ERROR </home/vipa/repositories/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 77:37-77:56>:\nField \'label\' not found\n[0m    age = symbiont_tree.age, label = [31msymbiont_tree.label[0m[0m,\n")
                        ; exit 1,
                    repertoire = rootRep,
                    history = "" }
              in
              ReturnType1
                { lambda = lambda, mu = mu, beta = beta, tree = historyTree }
in
let anon38: {dMean: Float, ntips: Int, nhosts: Int, interactions: [Int], symbiont_tree: TreeLabeled, host_distances: [Float]} -> () -> ReturnType =
  lam input1.
    lam #var"5".
      rejectAccept
        input1.symbiont_tree
        input1.ntips
        input1.nhosts
        input1.interactions
        input1.host_distances
        input1.dMean
in
anon38 input {}
