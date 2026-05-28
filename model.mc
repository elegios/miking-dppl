mexpr
let and: Bool -> Bool -> Bool =
  lam a90: Bool.
    lam b30: Bool.
      match
        a90
      with
        true
      then
        b30
      else
        false
in
let isNaN: Float -> Bool =
  lam a89: Float.
    match
      eqf a89 a89
    with
      true
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
        match
          s
        with
          ""
        then
          ""
        else match
          s
        with
          [ a2 ]
        then
          [ f a2 ]
        else match
          s
        with
          [ a3 ] ++ ss
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
          match
            s1
          with
            ""
          then
            ""
          else match
            s1
          with
            [ a6 ]
          then
            [ f1 i a6 ]
          else match
            s1
          with
            [ a7 ] ++ ss1
          in
          cons (f1 i a7) (rec1 f1 (addi i 1) ss1)
in
let mapi1 = lam f27.
    lam s13.
      rec1 f27 0 s13 in
let iteri1 =
  lam f26.
    lam s12.
      let #var"22" = mapi1 f26 s12 in
      {}
in
recursive
  let rec2: all a8. all a9. (a8 -> a9 -> a8) -> a8 -> [a9] -> a8 =
    lam f2.
      lam acc.
        lam s2.
          match
            s2
          with
            ""
          then
            acc
          else match
            s2
          with
            [ a10 ] ++ ss2
          in
          rec2 f2 (f2 acc a10) ss2
in
let foldl1 =
  lam f25.
    lam acc20.
      lam s11.
        rec2 f25 acc20 s11
in
recursive
  let rec3: all a11. (Int -> a11) -> Int -> [a11] -> [a11] =
    lam f3.
      lam i1.
        lam acc1.
          match
            geqi i1 0
          with
            true
          then
            rec3 f3 (subi i1 1) (cons (f3 i1) acc1)
          else
            acc1
in
let create1 = lam l10.
    lam f24.
      rec3 f24 (subi l10 1) ""
in
type Option a12 in
con Some: all a13. a13 -> Option a13 in
con None: all a14. () -> Option a14 in
type Either a15 b in
con Left: all a16. all b1. a16 -> Either a16 b1 in
con Right: all a17. all b2. b2 -> Either a17 b2 in
let anon: all a88. a88 -> Int -> a88 = lam v2.
    lam #var"21".
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
        match
          fb
        with
          None _
        then
          ""
        else match
          fb
        with
          Some (x, b11)
        in
        cons x (unfoldr f4 b11)
in
let anon1: Int -> Int -> Int -> Option (Int, Int) =
  lam e4.
    lam by1.
      lam b29.
        match
          leqi e4 b29
        with
          true
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
    lam acc18: (a86, [b28]).
      lam x212.
        match
          acc18
        with
          (acc19, [ x161 ] ++ xs1)
        then
          (f23 acc19 x161 x212, xs1)
        else
          error "foldl2: Cannot happen!"
in
let anon2: all c12. all b27. all a85. (a85 -> b27 -> c12 -> a85) -> a85 -> c12 -> b27 -> a85 =
  lam f22.
    lam acc17.
      lam x160.
        lam x211.
          f22 acc17 x211 x160
in
recursive
  let foldl2: all a19. all b3. all c1. (a19 -> b3 -> c1 -> a19) -> a19 -> [b3] -> [c1] -> a19 =
    lam f5: a19 -> b3 -> c1 -> a19.
      lam acc2: a19.
        lam seq1: [b3].
          lam seq2: [c1].
            match
              geqi (length seq1) (length seq2)
            with
              true
            then
              match
                foldl1 (g f5) (acc2, seq1) seq2
              with
                (acc3, _)
              in
              acc3
            else
              foldl2 (anon2 f5) acc2 seq2 seq1
in
recursive
  let work: all b4. all a20. (a20 -> Int -> b4 -> a20) -> a20 -> Int -> [b4] -> a20 =
    lam fn.
      lam acc4.
        lam i2.
          lam s3.
            match
              s3
            with
              [ e ] ++ rest
            then
              work fn (fn acc4 i2 e) (addi i2 1) rest
            else
              acc4
in
let foldli: all a84. all b26. (a84 -> Int -> b26 -> a84) -> a84 -> [b26] -> a84 =
  lam fn1: a84 -> Int -> b26 -> a84.
    lam initAcc: a84.
      lam seq11: [b26].
        work fn1 initAcc 0 seq11
in
let anon3: all c11. all b25. all a83. (a83 -> b25 -> c11) -> [c11] -> a83 -> b25 -> [c11] =
  lam f21.
    lam acc16.
      lam x159.
        lam x210.
          snoc acc16 (f21 x159 x210)
in
let zipWith: all a82. all b24. all c10. (a82 -> b24 -> c10) -> [a82] -> [b24] -> [c10] = lam f20: a82 -> b24 -> c10.
    foldl2 (anon3 f20) ""
in
recursive
  let any: all a21. (a21 -> Bool) -> [a21] -> Bool =
    lam p: a21 -> Bool.
      lam seq: [a21].
        match
          null seq
        with
          true
        then
          false
        else match
          p (head seq)
        with
          true
        then
          true
        else
          any p (tail seq)
in
let join: all a81. [[a81]] -> [a81] = lam seqs: [[a81]].
    foldl1 concat "" seqs
in
recursive
  let work1: all a22. (a22 -> Bool) -> [a22] -> [a22] -> [a22] -> ([a22], [a22]) =
    lam p1.
      lam l.
        lam r.
          lam seq3.
            match
              seq3
            with
              ""
            then
              (l, r)
            else match
              seq3
            with
              [ s4 ] ++ seq4
            in
            match
                p1 s4
              with
                true
              then
                work1 p1 (cons s4 l) r seq4
              else
                work1 p1 l (cons s4 r) seq4
in
let partition: all a80. (a80 -> Bool) -> [a80] -> ([a80], [a80]) =
  lam p4: a80 -> Bool.
    lam seq10: [a80].
      work1 p4 "" "" (reverse seq10)
in
let anon4: all a79. (a79 -> a79 -> Int) -> a79 -> a79 -> Bool =
  lam cmp4.
    lam h4.
      lam x158.
        lti (cmp4 x158 h4) 0
in
recursive
  let quickSort: all a23. (a23 -> a23 -> Int) -> [a23] -> [a23] =
    lam cmp: a23 -> a23 -> Int.
      lam seq5: [a23].
        match
          null seq5
        with
          true
        then
          seq5
        else
          let h = head seq5 in
          let t = tail seq5 in
          let lr = partition (anon4 cmp h) t in
          concat (quickSort cmp lr.0) (cons h (quickSort cmp lr.1))
in
let eitherEither: all a78. all b23. all c9. (a78 -> c9) -> (b23 -> c9) -> Either a78 b23 -> c9 =
  lam lf: a78 -> c9.
    lam rf: b23 -> c9.
      lam e2: Either a78 b23.
        match
          e2
        with
          Left content
        then
          lf content
        else match
          e2
        with
          Right content1
        in
        rf content1
in
type ExtArrKind a24 in
type ExtArr a25 in
external externalExtArrMakeUninit : all a26. ExtArrKind a26 -> Int -> ExtArr a26
in
external externalExtArrKind : all a27. ExtArr a27 -> ExtArrKind a27
in
external externalExtArrLength : all a28. ExtArr a28 -> Int in
external externalExtArrGet : all a29. ExtArr a29 -> Int -> a29
in
external externalExtArrSet! : all a30. ExtArr a30 -> Int -> a30 -> ()
in
external extArrKindFloat64 : ExtArrKind Float in
let extArrLength: all a76. ExtArr a76 -> Int = lam a77: ExtArr a76.
    externalExtArrLength a77
in
let extArrGetExn: all a74. ExtArr a74 -> Int -> a74 =
  lam a75: ExtArr a74.
    lam i20: Int.
      externalExtArrGet a75 i20
in
let extArrOfSeq: all a72. ExtArrKind a72 -> [a72] -> ExtArr a72 =
  lam kind1: ExtArrKind a72.
    lam seq9: [a72].
      let a73 = externalExtArrMakeUninit kind1 (length seq9) in
      let #var"20" = iteri1 (externalExtArrSet a73) seq9 in
      a73
in
type CBLASLayout in
external cblasRowMajor : CBLASLayout in
type CBLASTranspose in
external cblasNoTrans : CBLASTranspose in
external externalCblasCopy : all a31. Int -> ExtArr a31 -> Int -> ExtArr a31 -> Int -> ()
in
external externalCblasScal : all a32. Int -> a32 -> ExtArr a32 -> Int -> ()
in
external externalCblasGemm : all a33. CBLASLayout -> CBLASTranspose -> CBLASTranspose -> Int -> Int -> Int -> a33 -> ExtArr a33 -> Int -> ExtArr a33 -> Int -> a33 -> ExtArr a33 -> Int -> ()
in
type MatError in
con DimensionMismatch: () -> MatError in
con NotSquare: () -> MatError in
let matErrorToString: MatError -> [Char] =
  lam err3: MatError.
    let #var"X14" = err3 in
    match
      #var"X14"
    with
      DimensionMismatch _
    then
      "Dimension mismatch"
    else match
      #var"X14"
    with
      NotSquare _
    in
    "Not square"
in
type Mat a34 =
  {m: Int, n: Int, arr: ExtArr a34} in
let matMakeUninit: all a71. ExtArrKind a71 -> Int -> Int -> Mat a71 =
  lam kind: ExtArrKind a71.
    lam m3: Int.
      lam n4: Int.
        { n = n4,
          arr = externalExtArrMakeUninit kind (muli m3 n4),
          m = m3 }
in
let matGetExn: all a69. Mat a69 -> Int -> Int -> a69 =
  lam a70: Mat a69.
    lam i19: Int.
      lam j1: Int.
        externalExtArrGet a70.arr (addi (muli i19 a70.n) j1)
in
let matSetExn: all a67. Mat a67 -> Int -> Int -> a67 -> () =
  lam a68: Mat a67.
    lam i18: Int.
      lam j: Int.
        lam v: a67.
          externalExtArrSet a68.arr (addi (muli i18 a68.n) j) v
in
let matFromArrExn: all a65. Int -> Int -> ExtArr a65 -> Mat a65 =
  lam m2: Int.
    lam n3: Int.
      lam a66: ExtArr a65.
        match
          eqi (muli m2 n3) (extArrLength a66)
        with
          true
        then
          { n = n3, arr = a66, m = m2 }
        else
          error "matFromArrExn: dimensions mismatch"
in
let matHasSameShape2 =
  lam a64.
    lam b22.
      and (eqi a64.m b22.m) (eqi a64.n b22.n)
in
let matHasSameShape3 =
  lam a63.
    lam b21.
      lam c8.
        and (matHasSameShape2 a63 b21) (matHasSameShape2 b21 c8)
in
let matIsSquare = lam a62.
    eqi a62.m a62.n in
external externalMatTranspose : Int -> Int -> ExtArr Float -> ExtArr Float -> ()
in
let matTranposeNoAlloc: Mat Float -> Mat Float -> Either MatError () =
  lam a61: Mat Float.
    lam b20: Mat Float.
      match
        and (eqi a61.m b20.n) (eqi a61.n b20.m)
      with
        true
      then
        let #var"19" = externalMatTranspose a61.m a61.n a61.arr b20.arr
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
  lam a60: Mat Float.
    lam b19: Mat Float.
      lam c7: Mat Float.
        match
          matHasSameShape3 a60 b19 c7
        with
          true
        then
          let #var"18" = externalMatElemMul a60.m a60.n a60.arr b19.arr c7.arr
          in
          Right
            {}
        else
          Left
            (DimensionMismatch
               {})
in
let matTranspose: Mat Float -> Mat Float =
  lam a59: Mat Float.
    let b18 = matMakeUninit (externalExtArrKind a59.arr) a59.n a59.m
    in
    let #var"17" = matTranposeNoAlloc a59 b18 in
    b18
in
let matElemMul: Mat Float -> Mat Float -> Either MatError (Mat Float) =
  lam a58: Mat Float.
    lam b17: Mat Float.
      match
        matHasSameShape2 a58 b17
      with
        true
      then
        let c6 = matMakeUninit (externalExtArrKind a58.arr) a58.m a58.n
        in
        let #var"16" = matElemMulNoAlloc a58 b17 c6 in
        Right
          c6
      else
        Left
          (DimensionMismatch
             {})
in
let anon5: MatError -> Mat Float = lam err2.
    error (matErrorToString err2)
in
let anon6: Mat Float -> Mat Float = lam x157.
    x157 in
let matElemMulExn: Mat Float -> Mat Float -> Mat Float =
  lam a57: Mat Float.
    lam b16: Mat Float.
      eitherEither anon5 anon6 (matElemMul a57 b16)
in
let matScale: Float -> Mat Float -> Mat Float =
  lam s9: Float.
    lam a56: Mat Float.
      let m1 = a56.m in
      let n2 = a56.n in
      let b15 = matMakeUninit (externalExtArrKind a56.arr) m1 n2 in
      let mn = muli m1 n2 in
      let #var"14" = externalCblasCopy mn a56.arr 1 b15.arr 1 in
      let #var"15" = externalCblasScal mn s9 b15.arr 1 in
      b15
in
let matMul: Mat Float -> Mat Float -> Either MatError (Mat Float) =
  lam a55: Mat Float.
    lam b14: Mat Float.
      let m = a55.m in
      let n1 = b14.n in
      let k2 = a55.n in
      match
        eqi k2 b14.m
      with
        true
      then
        let c5 = matMakeUninit (externalExtArrKind b14.arr) m n1 in
        let #var"13" =
          externalCblasGemm
            cblasRowMajor
            cblasNoTrans
            cblasNoTrans
            m
            n1
            k2
            1.
            a55.arr
            k2
            b14.arr
            n1
            0.
            c5.arr
            n1
        in
        Right
          c5
      else
        Left
          (DimensionMismatch
             {})
in
let anon7: MatError -> Mat Float = lam err1.
    error (matErrorToString err1)
in
let anon8: Mat Float -> Mat Float = lam x156.
    x156 in
let matMulExn: Mat Float -> Mat Float -> Mat Float =
  lam a54: Mat Float.
    lam b13: Mat Float.
      eitherEither anon7 anon8 (matMul a54 b13)
in
external externalMatExp : Int -> Int -> ExtArr Float -> ExtArr Float
in
let matExp: Mat Float -> Either MatError (Mat Float) =
  lam a53: Mat Float.
    match
      matIsSquare a53
    with
      true
    then
      Right
        { a53 with arr = externalMatExp a53.m a53.n a53.arr }
    else
      Left
        (NotSquare
           {})
in
let anon9: MatError -> Mat Float = lam err.
    error (matErrorToString err)
in
let anon10: Mat Float -> Mat Float = lam x155.
    x155 in
let matExpExn: Mat Float -> Mat Float =
  lam a52: Mat Float.
    eitherEither anon9 anon10 (matExp a52)
in
recursive
  let work2: all a35. Int -> (Int -> a35 -> a35) -> Int -> a35 -> a35 =
    lam bound.
      lam f6.
        lam i3.
          lam acc5.
            match
              lti i3 bound
            with
              true
            then
              work2 bound f6 (addi i3 1) (f6 i3 acc5)
            else
              acc5
in
let _iterateni = lam bound1.
    lam f19.
      work2 bound1 f19 0
in
let seqSnoc = snoc in
let seqCons = cons in
let seqConcat = concat in
let seqLength = length in
let seqMap = map1 in
let seqZipWith = zipWith in
let seqSubsequence = subsequence in
let seqFoldl = foldl1 in
let seqFoldli = foldli in
let seqAny = any in
let mathExp = exp in
let mathLog = log in
type Matrix #var"X" =
  Mat #var"X" in

let anon11: Matrix Float -> Int -> Float -> Float =
  lam t4.
    lam i17.
      lam acc15.
        addf acc15 (extArrGetExn t4.arr i17)
in
let matMean =
  lam t3.
    let sum = _iterateni (muli t3.m t3.n) (anon11 t3) 0. in
    divf sum (int2float (muli t3.m t3.n))
in
let anon12: all a51. Mat a51 -> Int -> Mat a51 -> Int -> Int -> () =
  lam matrix1.
    lam r7.
      lam new1.
        lam i16.
          lam c4.
            matSetExn new1 0 i16 (matGetExn matrix1 r7 (subi c4 1))
in
let matRowCols =
  lam matrix.
    lam row3.
      lam cols3.
        let r6 = subi row3 1 in
        let new =
          matMakeUninit (externalExtArrKind matrix.arr) 1 (length cols3)
        in
        let #var"12" = iteri1 (anon12 matrix r6 new) cols3 in
        new
in
let x1: all #var"B10". all #var"A10". (#var"A10" -> #var"B10" -> #var"A10") -> #var"A10" -> #var"B10" -> #var"A10" =
  lam f18.
    lam a50.
      lam b12: #var"B10".
        let x154: #var"A10" = f18 a50 b12 in
        x154
in
let x2: all #var"B9". all #var"A9". (#var"A9" -> Int -> #var"B9" -> #var"A9") -> #var"A9" -> Int -> #var"B9" -> #var"A9" =
  lam f17.
    lam a49.
      lam idx7.
        lam b10: #var"B9".
          let x153: #var"A9" = f17 a49 (addi idx7 1) b10 in
          x153
in
let x3: all #var"B8". all #var"A8". (#var"A8" -> Int -> #var"B8" -> #var"A8") -> #var"A8" -> Int -> #var"B8" -> #var"A8" =
  lam f16.
    lam a48.
      lam idx6: Int.
        x2 f16 a48 idx6
in
let x4: all #var"C2". all #var"B7". all #var"A7". (#var"A7" -> #var"B7" -> #var"C2") -> #var"A7" -> #var"B7" -> #var"C2" =
  lam f15.
    lam a47.
      lam b9: #var"B7".
        let x152: #var"C2" = f15 a47 b9 in
        x152
in
let x5: all #var"X13". (#var"X13" -> #var"X13" -> Int) -> #var"X13" -> #var"X13" -> Int =
  lam cmp3.
    lam a46.
      lam b8: #var"X13".
        let x151: Int = cmp3 a46 b8 in
        x151
in
let ifCont = lam acc14.
    lam #var"11": Int.
      acc14 in
let exp1: Float -> Float = lam x150: Float.
    mathExp x150 in
let log1: Float -> Float = lam x149: Float.
    mathLog x149 in
let cons1: all #var"X12". #var"X12" -> [#var"X12"] -> [#var"X12"] =
  lam e1: #var"X12".
    lam s8: [#var"X12"].
      seqCons e1 s8
in
let rep: all #var"X11". Int -> #var"X11" -> [#var"X11"] =
  lam count: Int.
    lam elem1: #var"X11".
      make count elem1
in
let concat1: all #var"X10". [#var"X10"] -> [#var"X10"] -> [#var"X10"] =
  lam l9: [#var"X10"].
    lam r5: [#var"X10"].
      seqConcat l9 r5
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
    lam f14: #var"A6" -> #var"B6".
      seqMap f14 s7
in
let anon13: all #var"B5". all #var"A5". (#var"A5" -> #var"B5" -> #var"A5") -> #var"A5" -> #var"B5" -> #var"A5" = lam f13.
    lam a45: #var"A5".
      x1 f13 a45
in
let fold: all #var"A4". all #var"B4". (#var"A4" -> #var"B4" -> #var"A4") -> #var"A4" -> [#var"B4"] -> #var"A4" =
  lam f12: #var"A4" -> #var"B4" -> #var"A4".
    lam init1: #var"A4".
      lam seq8: [#var"B4"].
        seqFoldl (anon13 f12) init1 seq8
in
let anon14: all #var"B3". all #var"A3". (#var"A3" -> Int -> #var"B3" -> #var"A3") -> #var"A3" -> Int -> #var"B3" -> #var"A3" = lam f11.
    lam a44: #var"A3".
      x3 f11 a44
in
let foldi: all #var"A2". all #var"B2". (#var"A2" -> Int -> #var"B2" -> #var"A2") -> #var"A2" -> [#var"B2"] -> #var"A2" =
  lam f10: #var"A2" -> Int -> #var"B2" -> #var"A2".
    lam init: #var"A2".
      lam seq7: [#var"B2"].
        seqFoldli (anon14 f10) init seq7
in
let anon15: all #var"C1". all #var"B1". all #var"A1". (#var"A1" -> #var"B1" -> #var"C1") -> #var"A1" -> #var"B1" -> #var"C1" = lam f9.
    lam a43: #var"A1".
      x4 f9 a43
in
let zipWith1: all #var"A". all #var"B". all #var"C". (#var"A" -> #var"B" -> #var"C") -> [#var"A"] -> [#var"B"] -> [#var"C"] =
  lam f8: #var"A" -> #var"B" -> #var"C".
    lam a42: [#var"A"].
      lam b7: [#var"B"].
        seqZipWith (anon15 f8) a42 b7
in
let any1: all #var"X6". (#var"X6" -> Bool) -> [#var"X6"] -> Bool =
  lam f7: #var"X6" -> Bool.
    lam l5: [#var"X6"].
      seqAny f7 l5
in
let anon16: all #var"X5". (#var"X5" -> #var"X5" -> Int) -> #var"X5" -> #var"X5" -> Int = lam cmp2.
    lam a41: #var"X5".
      x5 cmp2 a41
in
let qSort: all #var"X4". (#var"X4" -> #var"X4" -> Int) -> [#var"X4"] -> [#var"X4"] =
  lam cmp1: #var"X4" -> #var"X4" -> Int.
    lam l4: [#var"X4"].
      quickSort (anon16 cmp1) l4
in
let anon17: [Int] -> Int -> Bool -> [Int] =
  lam acc13: [Int].
    lam idx5: Int.
      lam elem: Bool.
        let x148: [Int] =
          match
            elem
          with
            true
          then
            seqSnoc acc13 idx5
          else
            ifCont acc13 0
        in
        x148
in
let whichTrue: [Bool] -> [Int] = lam s6: [Bool].
    foldi anon17 "" s6
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
  lam a40: Matrix Float.
    lam b6: Matrix Float.
      matMulExn a40 b6
in
let mtxElemMul: Matrix Float -> Matrix Float -> Matrix Float =
  lam a39: Matrix Float.
    lam b5: Matrix Float.
      matElemMulExn a39 b5
in
let mtxMean: Matrix Float -> Float = lam mtx1: Matrix Float.
    matMean mtx1
in
let mathIsNaN = isNaN in
let row: all a38. [a38] -> Int -> Int -> [a38] =
  lam l3.
    lam c3.
      lam i15.
        let rs = muli i15 c3 in
        let re = addi rs c3 in
        subsequence l3 rs c3
in
let seqNest: all a37. [a37] -> Int -> Int -> [[a37]] =
  lam l2: [a37].
    lam r4: Int.
      lam c2: Int.
        map1 (row l2 c2) (range 0 r4 1)
in
let delta =
  lam k1.
    lam x147.
      match
        eqi k1 x147
      with
        true
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
  lam seq6: [#var"X1"].
    lam rows: Int.
      lam cols: Int.
        seqNest seq6 rows cols
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
  lam qMatrix3: Matrix Float.
    let q1 = negf (mtxGet 1 1 qMatrix3) in
    let q2 = negf (mtxGet 2 2 qMatrix3) in
    let q3 = negf (mtxGet 3 3 qMatrix3) in
    EmbeddedMarkovChainMatrix1
      { totalRates = [ q1,
            q2,
            q3 ],
        transitionProbs =
          [ [ 0., 1., 0. ],
            [ divf (mtxGet 2 1 qMatrix3) q2,
              0.,
              divf (mtxGet 2 3 qMatrix3) q2 ],
            [ 0., 1., 0. ] ],
        mat = qMatrix3 }
in
let is2: Int -> Bool = lam x146: Int.
    eqi x146 2 in
recursive
  let ones: Int -> [Float] =
    lam nOnes: Int.
      match
        gti nOnes 0
      with
        true
      then
        cons1 1. (ones (subi nOnes 1))
      else
        ""
in
let anon18: Int -> Int -> Int =
  lam acc12: Int.
    lam h3: Int.
      let x145: Int =
        match
          eqi h3 2
        with
          true
        then
          addi acc12 1
        else
          acc12
      in
      x145
in
let n2s: [Int] -> Int = lam repertoire2: [Int].
    fold anon18 0 repertoire2
in
let updateRepertoire: [Int] -> Event -> Int -> [Int] =
  lam currRep8: [Int].
    lam event3: Event.
      lam nhosts15: Int.
        let hostIndex4 =
          let target89 = event3 in
          match
            target89
          with
            Event1 x144
          then
            x144.host
          else
            let #var"1" =
              print
                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
            in
            exit 1
        in
        paste0
          [ slice currRep8 1 hostIndex4,
            [ let target88 = event3 in
              match
                target88
              with
                Event1 x143
              then
                x143.toState
              else
                let #var"1" =
                  print
                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                in
                exit 1 ],
            slice currRep8 (addi hostIndex4 1) (addi nhosts15 1) ]
in
let sampleNextEvent: Int -> EmbeddedMarkovChainMatrix -> Int =
  lam currState1: Int.
    lam embeddedQMatrix4: EmbeddedMarkovChainMatrix.
      match
        eqi currState1 0
      with
        true
      then
        1
      else match
        eqi currState1 2
      with
        true
      then
        1
      else
        let param9 =
          get
            (let target87 = embeddedQMatrix4 in
             match
               target87
             with
               EmbeddedMarkovChainMatrix1 x142
             then
               x142.transitionProbs
             else
               let #var"1" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 75:18-75:49>:\nField \'transitionProbs\' not found\n[0m      let param = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1];\n"
               in
               exit 1)
            (subi (addi currState1 1) 1)
        in
        let nextState3 = assume
            (Categorical param9) in
        nextState3
in
let makeStateMessage: Int -> [Float] =
  lam interaction: Int.
    match
      match
        geqi interaction 0
      with
        true
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
          match
            leqi i4 max
          with
            true
          then
            let stateMsg = makeStateMessage (get obsRepertoire (subi i4 1))
            in
            concat1 stateMsg (observationMessage obsRepertoire (addi i4 1) max)
          else
            ""
in
recursive
  let ifCont1 =
    lam tree.
      lam qMatrix.
        lam interactions.
          lam nhosts.
            lam #var"": Int.
              let left =
                postorderTraverse
                  (let target9 = tree in
                   match
                     target9
                   with
                     Node x23
                   then
                     x23.left
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 19:31-19:40>:\nField \'left\' not found\n[0m  let left = postorderTraverse([31mtree.left[0m[0m, qMatrix, interactions, nhosts);\n"
                     in
                     exit 1)
                  qMatrix
                  interactions
                  nhosts
              in
              let right =
                postorderTraverse
                  (let target8 = tree in
                   match
                     target8
                   with
                     Node x22
                   then
                     x22.right
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 20:32-20:42>:\nField \'right\' not found\n[0m  let right = postorderTraverse([31mtree.right[0m[0m, qMatrix, interactions, nhosts);\n"
                     in
                     exit 1)
                  qMatrix
                  interactions
                  nhosts
              in
              let leftKernel =
                mtxExp
                  (mtxSclrMul
                     (subf
                        (let target6 = tree in
                         match
                           target6
                         with
                           Node x18
                         then
                           x18.age
                         else match
                           target6
                         with
                           Leaf x19
                         then
                           x19.age
                         else
                           let #var"1" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:37-23:45>:\nField \'age\' not found\n[0m  let leftKernel = mtxExp(mtxSclrMul([31mtree.age[0m[0m-left.age, qMatrix));\n"
                           in
                           exit 1)
                        (let target7 = left in
                         match
                           target7
                         with
                           MsgNode x20
                         then
                           x20.age
                         else match
                           target7
                         with
                           MsgLeaf x21
                         then
                           x21.age
                         else
                           let #var"1" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:46-23:54>:\nField \'age\' not found\n[0m  let leftKernel = mtxExp(mtxSclrMul(tree.age-[31mleft.age[0m[0m, qMatrix));\n"
                           in
                           exit 1))
                     qMatrix)
              in
              let rightKernel =
                mtxExp
                  (mtxSclrMul
                     (subf
                        (let target4 = tree in
                         match
                           target4
                         with
                           Node x14
                         then
                           x14.age
                         else match
                           target4
                         with
                           Leaf x15
                         then
                           x15.age
                         else
                           let #var"1" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:38-24:46>:\nField \'age\' not found\n[0m  let rightKernel = mtxExp(mtxSclrMul([31mtree.age[0m[0m-right.age, qMatrix));\n"
                           in
                           exit 1)
                        (let target5 = right in
                         match
                           target5
                         with
                           MsgNode x16
                         then
                           x16.age
                         else match
                           target5
                         with
                           MsgLeaf x17
                         then
                           x17.age
                         else
                           let #var"1" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:47-24:56>:\nField \'age\' not found\n[0m  let rightKernel = mtxExp(mtxSclrMul(tree.age-[31mright.age[0m[0m, qMatrix));\n"
                           in
                           exit 1))
                     qMatrix)
              in
              let leftBackwardKernel = mtxTrans leftKernel in
              let rightBackwardKernel = mtxTrans rightKernel in
              let leftInMsg =
                mtxMul
                  (let target3 = left in
                   match
                     target3
                   with
                     MsgNode x12
                   then
                     x12.outMsg
                   else match
                     target3
                   with
                     MsgLeaf x13
                   then
                     x13.outMsg
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 30:25-30:36>:\nField \'outMsg\' not found\n[0m  let leftInMsg = mtxMul([31mleft.outMsg[0m[0m, leftBackwardKernel);\n"
                     in
                     exit 1)
                  leftBackwardKernel
              in
              let rightInMsg =
                mtxMul
                  (let target2 = right in
                   match
                     target2
                   with
                     MsgNode x10
                   then
                     x10.outMsg
                   else match
                     target2
                   with
                     MsgLeaf x11
                   then
                     x11.outMsg
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 31:26-31:38>:\nField \'outMsg\' not found\n[0m  let rightInMsg = mtxMul([31mright.outMsg[0m[0m, rightBackwardKernel);\n"
                     in
                     exit 1)
                  rightBackwardKernel
              in
              let outMsg = mtxElemMul leftInMsg rightInMsg in
              MsgNode
                { age =
                    let target = tree in
                    match
                      target
                    with
                      Node x6
                    then
                      x6.age
                    else match
                      target
                    with
                      Leaf x7
                    then
                      x7.age
                    else
                      let #var"1" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 36:10-36:18>:\nField \'age\' not found\n[0m    age = [31mtree.age[0m[0m, label = tree.label,\n"
                      in
                      exit 1,
                  left = left,
                  right = right,
                  label =
                    let target1 = tree in
                    match
                      target1
                    with
                      Node x8
                    then
                      x8.label
                    else match
                      target1
                    with
                      Leaf x9
                    then
                      x9.label
                    else
                      let #var"1" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 36:28-36:38>:\nField \'label\' not found\n[0m    age = tree.age, label = [31mtree.label[0m[0m,\n"
                      in
                      exit 1,
                  outMsg = outMsg,
                  leftInMsg = leftInMsg,
                  rightInMsg = rightInMsg,
                  leftKernel = leftKernel,
                  rightKernel = rightKernel }
  let postorderTraverse: TreeLabeled -> Matrix Float -> [[Int]] -> Int -> MsgTree =
    lam tree1: TreeLabeled.
      lam qMatrix1: Matrix Float.
        lam interactions1: [[Int]].
          lam nhosts1: Int.
            match
              match
                tree1
              with
                Leaf _
              then
                true
              else
                false
            with
              true
            then
              let outmsg =
                mtxCreate
                  nhosts1
                  3
                  (observationMessage
                     (get
                        interactions1
                        (subi
                           (let target12 = tree1 in
                            match
                              target12
                            with
                              Node x28
                            then
                              x28.label
                            else match
                              target12
                            with
                              Leaf x29
                            then
                              x29.label
                            else
                              let #var"1" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 9:70-9:80>:\nField \'label\' not found\n[0m    let outmsg = mtxCreate(nhosts, 3, observationMessage(interactions[[31mtree.label[0m[0m], 1, nhosts));\n"
                              in
                              exit 1)
                           1))
                     1
                     nhosts1)
              in
              let leafInts =
                get
                  interactions1
                  (subi
                     (let target11 = tree1 in
                      match
                        target11
                      with
                        Node x26
                      then
                        x26.label
                      else match
                        target11
                      with
                        Leaf x27
                      then
                        x27.label
                      else
                        let #var"1" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 10:32-10:42>:\nField \'label\' not found\n[0m    let leafInts = interactions[[31mtree.label[0m[0m];\n"
                        in
                        exit 1)
                     1)
              in
              MsgLeaf
                { age = 0.,
                  label =
                    let target10 = tree1 in
                    match
                      target10
                    with
                      Node x24
                    then
                      x24.label
                    else match
                      target10
                    with
                      Leaf x25
                    then
                      x25.label
                    else
                      let #var"1" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 13:14-13:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                      in
                      exit 1,
                  outMsg =
                    mtxCreate nhosts1 3 (observationMessage leafInts 1 nhosts1),
                  interactions = leafInts }
            else
              ifCont1 tree1 qMatrix1 interactions1 nhosts1 0
in
let categoricalLogPdf: Int -> [Float] -> Float =
  lam x141: Int.
    lam params: [Float].
      match
        match
          geqi x141 0
        with
          true
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
let anon19: [Int] -> Matrix Float -> Float -> Int -> Float =
  lam x139.
    lam samplingProb2.
      lam acc11: Float.
        lam i12: Int.
          let x140: Float =
            let param8 = mtx3ToSeq samplingProb2 i12 in
            addf acc11 (categoricalLogPdf (get x139 (subi i12 1)) param8)
          in
          x140
in
let anon20: Int -> Int -> Int = lam start9.
    lam idx4.
      addi idx4 start9
in
let getRepertoireDebt: [Int] -> Matrix Float -> Int -> Float =
  lam x138: [Int].
    lam samplingProb1: Matrix Float.
      lam nhosts14: Int.
        fold
          (anon19 x138 samplingProb1)
          0.
          (let start8 = 1 in
           let end5 = nhosts14 in
           create1 (addi (subi end5 start8) 1) (anon20 start8))
in
let anon21: Int -> Int -> Int =
  lam acc10: Int.
    lam h2: Int.
      let x137: Int =
        match
          eqi h2 2
        with
          true
        then
          addi acc10 1
        else
          acc10
      in
      x137
in
recursive
  let ifCont2 =
    lam currRep.
      lam eventSeq.
        lam eventIndex.
          lam nEvents.
            lam nhosts2.
              lam event.
                lam #var"2": Int.
                  let newRep = updateRepertoire currRep event nhosts2 in
                  allTimesValidBranch newRep eventSeq (addi eventIndex 1) nEvents nhosts2
  let allTimesValidBranch: [Int] -> [Event] -> Int -> Int -> Int -> Bool =
    lam currRep1: [Int].
      lam eventSeq1: [Event].
        lam eventIndex1: Int.
          lam nEvents1: Int.
            lam nhosts3: Int.
              match
                gti eventIndex1 nEvents1
              with
                true
              then
                true
              else
                let event1 = get eventSeq1 (subi eventIndex1 1) in
                match
                  eqi
                    (let target13 = event1 in
                     match
                       target13
                     with
                       Event1 x30
                     then
                       x30.fromState
                     else
                       let #var"1" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 146:7-146:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n"
                       in
                       exit 1)
                    2
                with
                  true
                then
                  let n2s1 = fold anon21 0 currRep1 in
                  match
                    eqi n2s1 1
                  with
                    true
                  then
                    false
                  else
                    ifCont3 currRep1 eventSeq1 eventIndex1 nEvents1 nhosts3 event1 0
                else
                  ifCont2 currRep1 eventSeq1 eventIndex1 nEvents1 nhosts3 event1 0
  let ifCont3 =
    lam currRep2.
      lam eventSeq2.
        lam eventIndex2.
          lam nEvents2.
            lam nhosts4.
              lam event2.
                lam #var"3": Int.
                  ifCont2 currRep2 eventSeq2 eventIndex2 nEvents2 nhosts4 event2 0
in
let anon22: Int -> Bool =
  lam i11: Int.
    let x136: Bool =
      match
        eqi i11 2
      with
        true
      then
        true
      else
        eqi i11 1
    in
    x136
in
let anon23: Int -> Bool = lam i10: Int.
    let x135: Bool = eqi i10 2 in
    x135
in
let getGainRate: [Int] -> Int -> ModelParams -> Float =
  lam repertoire1: [Int].
    lam hostIndex3: Int.
      lam modelParams15: ModelParams.
        let fromState5 = get repertoire1 (subi hostIndex3 1) in
        let toState3 = addi fromState5 1 in
        let baseRate1 =
          mtxGet
            (addi fromState5 1)
            (addi toState3 1)
            (let target85 =
               let target86 = modelParams15 in
               match
                 target86
               with
                 ModelParams1 x134
               then
                 x134.embeddedQMatrix
               else
                 let #var"1" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                 in
                 exit 1
             in
             match
               target85
             with
               EmbeddedMarkovChainMatrix1 x133
             then
               x133.mat
             else
               let #var"1" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
               in
               exit 1)
        in
        match
          eqi fromState5 0
        with
          true
        then
          let currentHosts = whichTrue (sapply repertoire1 anon22) in
          let dist =
            mtxMean
              (mtxRowCols
                 (let target81 = modelParams15 in
                  match
                    target81
                  with
                    ModelParams1 x129
                  then
                    x129.hostMetric
                  else
                    let #var"1" =
                      print
                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                    in
                    exit 1)
                 hostIndex3
                 currentHosts)
          in
          mulf
            baseRate1
            (pow
               (divf
                  dist
                  (let target79 = modelParams15 in
                   match
                     target79
                   with
                     ModelParams1 x127
                   then
                     x127.meanDist
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                     in
                     exit 1))
               (negf
                  (let target80 = modelParams15 in
                   match
                     target80
                   with
                     ModelParams1 x128
                   then
                     x128.beta
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                     in
                     exit 1)))
        else
          let currentHosts1 = whichTrue (sapply repertoire1 anon23) in
          let dist1 =
            mtxMean
              (mtxRowCols
                 (let target84 = modelParams15 in
                  match
                    target84
                  with
                    ModelParams1 x132
                  then
                    x132.hostMetric
                  else
                    let #var"1" =
                      print
                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                    in
                    exit 1)
                 hostIndex3
                 currentHosts1)
          in
          mulf
            baseRate1
            (pow
               (divf
                  dist1
                  (let target82 = modelParams15 in
                   match
                     target82
                   with
                     ModelParams1 x130
                   then
                     x130.meanDist
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                     in
                     exit 1))
               (negf
                  (let target83 = modelParams15 in
                   match
                     target83
                   with
                     ModelParams1 x131
                   then
                     x131.beta
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                     in
                     exit 1)))
in
let anon24: [Int] -> ModelParams -> Float -> Int -> Float =
  lam currRep7.
    lam modelParams14.
      lam acc9: Float.
        lam i9: Int.
          let x126: Float =
            let fromState4 = get currRep7 (subi i9 1) in
            match
              eqi fromState4 2
            with
              true
            then
              acc9
            else
              addf acc9 (getGainRate currRep7 i9 modelParams14)
          in
          x126
in
let anon25: Int -> Int -> Int = lam start7.
    lam idx3.
      addi idx3 start7
in
let getLossRate: [Int] -> Int -> ModelParams -> Float =
  lam repertoire: [Int].
    lam hostIndex2: Int.
      lam modelParams13: ModelParams.
        let fromState3 = get repertoire (subi hostIndex2 1) in
        match
          match
            eqi fromState3 2
          with
            true
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
                 let target78 = modelParams13 in
                 match
                   target78
                 with
                   ModelParams1 x125
                 then
                   x125.embeddedQMatrix
                 else
                   let #var"1" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                   in
                   exit 1
               in
               match
                 target77
               with
                 EmbeddedMarkovChainMatrix1 x124
               then
                 x124.mat
               else
                 let #var"1" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                 in
                 exit 1)
          in
          baseRate
in
let anon26: [Int] -> ModelParams -> Float -> Int -> Float =
  lam currRep6.
    lam modelParams12.
      lam acc8: Float.
        lam i8: Int.
          let x123: Float =
            let fromState2 = get currRep6 (subi i8 1) in
            match
              eqi fromState2 0
            with
              true
            then
              acc8
            else
              addf acc8 (getLossRate currRep6 i8 modelParams12)
          in
          x123
in
let anon27: Int -> Int -> Int = lam start6.
    lam idx2.
      addi idx2 start6
in
let getTotalRate: [Int] -> ModelParams -> Int -> Float =
  lam currRep5: [Int].
    lam modelParams11: ModelParams.
      lam nhosts13: Int.
        let gainRates =
          fold
            (anon24 currRep5 modelParams11)
            0.
            (let start5 = 1 in
             let end4 = nhosts13 in
             create1 (addi (subi end4 start5) 1) (anon25 start5))
        in
        let lossRates =
          fold
            (anon26 currRep5 modelParams11)
            0.
            (let start4 = 1 in
             let end3 = nhosts13 in
             create1 (addi (subi end3 start4) 1) (anon27 start4))
        in
        addf gainRates lossRates
in
let getRate: [Int] -> Event -> ModelParams -> Float =
  lam currRep4: [Int].
    lam nextEvent2: Event.
      lam modelParams10: ModelParams.
        let hostIndex1 =
          let target76 = nextEvent2 in
          match
            target76
          with
            Event1 x122
          then
            x122.host
          else
            let #var"1" =
              print
                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
            in
            exit 1
        in
        match
          gti
            (let target74 = nextEvent2 in
             match
               target74
             with
               Event1 x120
             then
               x120.fromState
             else
               let #var"1" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
               in
               exit 1)
            (let target75 = nextEvent2 in
             match
               target75
             with
               Event1 x121
             then
               x121.toState
             else
               let #var"1" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
               in
               exit 1)
        with
          true
        then
          getLossRate currRep4 hostIndex1 modelParams10
        else
          getGainRate currRep4 hostIndex1 modelParams10
in
recursive
  let fullModelWeight: Int -> [Int] -> [Int] -> Float -> Float -> [Event] -> Int -> Int -> ModelParams -> Float =
    lam nextIndex: Int.
      lam currRep3: [Int].
        lam finalRep: [Int].
          lam currAge: Float.
            lam finalAge: Float.
              lam eventSeq3: [Event].
                lam nEvents3: Int.
                  lam nhosts5: Int.
                    lam modelParams: ModelParams.
                      match
                        gti nextIndex nEvents3
                      with
                        true
                      then
                        let timePassed = subf currAge finalAge in
                        let totalLeavingRate = getTotalRate currRep3 modelParams nhosts5
                        in
                        mulf (negf timePassed) totalLeavingRate
                      else
                        let nextEvent = get eventSeq3 (subi nextIndex 1) in
                        let newAge =
                          let target14 = nextEvent in
                          match
                            target14
                          with
                            Event1 x31
                          then
                            x31.eventTime
                          else
                            let #var"1" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                            in
                            exit 1
                        in
                        let totalLeavingRate1 = getTotalRate currRep3 modelParams nhosts5
                        in
                        let thisRate = getRate currRep3 nextEvent modelParams in
                        let timePassed1 = subf currAge newAge in
                        let thisWeight =
                          subf
                            (log1 (divf thisRate totalLeavingRate1))
                            (mulf timePassed1 totalLeavingRate1)
                        in
                        let newRep1 = updateRepertoire currRep3 nextEvent nhosts5 in
                        addf
                          thisWeight
                          (fullModelWeight
                             (addi nextIndex 1)
                             newRep1
                             finalRep
                             newAge
                             finalAge
                             eventSeq3
                             nEvents3
                             nhosts5
                             modelParams)
in
let newParamFun =
  lam alpha2.
    lam epsilon1.
      lam a36: Float.
        let x119: Float =
          match
            gtf a36 epsilon1
          with
            true
          then
            match
              ltf a36 (subf 1. epsilon1)
            with
              true
            then
              mulf a36 alpha2
            else
              mulf (subf a36 epsilon1) alpha2
          else
            mulf (addf a36 epsilon1) alpha2
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
let anon28: Int -> Int -> Int = lam start3.
    lam idx1.
      addi idx1 start3
in
let anon29: Int -> [Float] -> Float -> Float -> Int -> Float =
  lam x115.
    lam param7.
      lam currProb1.
        lam nextProb1.
          lam i7: Int.
            let x116: Float =
              match
                eqi i7 x115
              with
                true
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
          match
            ltf currProb (subf 1. errMargin1)
          with
            true
          then
            let nextProb = mulf currProb (subf 1. lambda5) in
            let newParam =
              sapply
                (let start2 = 1 in
                 let end2 = length1 param6 in
                 create1 (addi (subi end2 start2) 1) (anon28 start2))
                (anon29 x114 param6 currProb nextProb)
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
              lam eventSeq4: [Event].
                lam embeddedQMatrix: EmbeddedMarkovChainMatrix.
                  match
                    gti nextIndex1 (length1 eventSeq4)
                  with
                    true
                  then
                    let timePassed2 = subf currAge1 finalAge1 in
                    let outRate =
                      get
                        (let target15 = embeddedQMatrix in
                         match
                           target15
                         with
                           EmbeddedMarkovChainMatrix1 x32
                         then
                           x32.totalRates
                         else
                           let #var"1" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                           in
                           exit 1)
                        (subi (addi currState 1) 1)
                    in
                    mulf (negf timePassed2) outRate
                  else
                    let nextEvent1 = get eventSeq4 (subi nextIndex1 1) in
                    let nextState =
                      let target19 = nextEvent1 in
                      match
                        target19
                      with
                        Event1 x36
                      then
                        x36.toState
                      else
                        let #var"1" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                        in
                        exit 1
                    in
                    let nextAge =
                      let target18 = nextEvent1 in
                      match
                        target18
                      with
                        Event1 x35
                      then
                        x35.eventTime
                      else
                        let #var"1" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n"
                        in
                        exit 1
                    in
                    let timePassed3 = subf currAge1 nextAge in
                    let outRate1 =
                      get
                        (let target17 = embeddedQMatrix in
                         match
                           target17
                         with
                           EmbeddedMarkovChainMatrix1 x34
                         then
                           x34.totalRates
                         else
                           let #var"1" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                           in
                           exit 1)
                        (subi (addi currState 1) 1)
                    in
                    let transProb =
                      get
                        (get
                           (let target16 = embeddedQMatrix in
                            match
                              target16
                            with
                              EmbeddedMarkovChainMatrix1 x33
                            then
                              x33.transitionProbs
                            else
                              let #var"1" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                              in
                              exit 1)
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
                         eventSeq4
                         embeddedQMatrix)
in
let anon30: [Int] -> [Int] -> Float -> Float -> [[Event]] -> ModelParams -> Float -> Int -> Float =
  lam fromRep2.
    lam toRep2.
      lam fromAge2.
        lam toAge2.
          lam eventSeqs2.
            lam modelParams9.
              lam acc7: Float.
                lam h1: Int.
                  let x108: Float =
                    let eventSeq5 = get eventSeqs2 (subi h1 1) in
                    let fromState1 = get fromRep2 (subi h1 1) in
                    let toState1 = get toRep2 (subi h1 1) in
                    addf
                      acc7
                      (hostIndepLikelihood
                         1
                         fromState1
                         toState1
                         fromAge2
                         toAge2
                         eventSeq5
                         (let target73 = modelParams9 in
                          match
                            target73
                          with
                            ModelParams1 x109
                          then
                            x109.embeddedQMatrix
                          else
                            let #var"1" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                            in
                            exit 1))
                  in
                  x108
in
let anon31: Int -> Int -> Int = lam start1.
    lam idx.
      addi idx start1
in
let independenceLikelihood: [Int] -> [Int] -> Float -> Float -> [[Event]] -> ModelParams -> Float =
  lam fromRep1: [Int].
    lam toRep1: [Int].
      lam fromAge1: Float.
        lam toAge1: Float.
          lam eventSeqs1: [[Event]].
            lam modelParams8: ModelParams.
              let unconditional1 =
                fold
                  (anon30 fromRep1 toRep1 fromAge1 toAge1 eventSeqs1 modelParams8)
                  0.
                  (let start = 1 in
                   let end1 = length1 eventSeqs1 in
                   create1 (addi (subi end1 start) 1) (anon31 start))
              in
              unconditional1
in
let anon32: Float -> Float -> Float =
  lam acc6: Float.
    lam val: Float.
      let x107: Float = addf acc6 val in
      x107
in
let anon33: Matrix Float -> Int -> Int -> Float =
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
            lam modelParams7: ModelParams.
              lam kernel: Matrix Float.
                let unconditional =
                  independenceLikelihood fromRep toRep fromAge toAge eventSeqs modelParams7
                in
                let logTotalTransProb = fold anon32 0. (zipWith1 (anon33 kernel) fromRep toRep)
                in
                let conditional = subf unconditional logTotalTransProb in
                conditional
in
type ReturnType in
con ReturnType1: {mu: Float, beta: Float, tree: HistoryTree, lambda: [Float]} -> ReturnType
in
let ifCont4 =
  lam tree4.
    lam rep4.
      lam branchSample3.
        lam #var"10": Int.
          HistoryLeaf
            { age =
                let target70 = tree4 in
                match
                  target70
                with
                  MsgNode x101
                then
                  x101.age
                else match
                  target70
                with
                  MsgLeaf x102
                then
                  x102.age
                else
                  let #var"1" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 158:12-158:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
                  in
                  exit 1,
              label =
                let target71 = tree4 in
                match
                  target71
                with
                  MsgNode x103
                then
                  x103.label
                else match
                  target71
                with
                  MsgLeaf x104
                then
                  x104.label
                else
                  let #var"1" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 159:14-159:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                  in
                  exit 1,
              repertoire = rep4,
              history =
                let target72 = branchSample3 in
                match
                  target72
                with
                  CorrectedBranchSample1 x105
                then
                  x105.history
                else
                  let #var"1" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 161:16-161:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n"
                  in
                  exit 1 }
in
let anon34: [Float] -> Int -> Dist(Int) = lam param4.
    lam x100.
      categoricalMove x100 param4
in
recursive
  let suggestRepAligned: Matrix Float -> Int -> Int -> [Int] =
    lam msg: Matrix Float.
      lam i5: Int.
        lam max1: Int.
          match
            leqi i5 max1
          with
            true
          then
            let param = mtx3ToSeq msg i5 in
            let x37 = assume
                (Categorical param) in
            cons1 x37 (suggestRepAligned msg (addi i5 1) max1)
          else
            ""
in
recursive
  let suggestRepUnaligned: Matrix Float -> Int -> Int -> [Int] =
    lam msg1: Matrix Float.
      lam i6: Int.
        lam max2: Int.
          match
            leqi i6 max2
          with
            true
          then
            let param1 = mtx3ToSeq msg1 i6 in
            let x38 = assume
                (Categorical param1) in
            paste0
              [ [ x38 ],
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
            match
              any1 is2 initialRep
            with
              true
            then
              initialRep
            else match
              lti depth _REP_REJECTION_DEPTH
            with
              true
            then
              let newRep2 = suggestRepUnaligned msg2 1 max3 in
              suggestRepRS msg2 max3 newRep2 (addi depth 1)
            else
              let foo = weight
                  (externalLog 0.) in
              initialRep
in
let ifCont5 =
  lam left4.
    lam right4.
      lam #var"9": Int.
        match
          geqf
            (let target68 = right4 in
             match
               target68
             with
               Event1 x98
             then
               x98.eventTime
             else
               let #var"1" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 288:6-288:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n"
               in
               exit 1)
            (let target69 = left4 in
             match
               target69
             with
               Event1 x99
             then
               x99.eventTime
             else
               let #var"1" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 288:25-288:39>:\nField \'eventTime\' not found\n[0m  if (right.eventTime >= [31mleft.eventTime[0m[0m) {\n"
               in
               exit 1)
        with
          true
        then
          1
        else
          negi 1
in
let ifCont6 =
  lam left3.
    lam right3.
      lam #var"8": Int.
        match
          isNaN1
            (let target67 = left3 in
             match
               target67
             with
               Event1 x97
             then
               x97.eventTime
             else
               let #var"1" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 285:12-285:26>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mleft.eventTime[0m[0m)) {\n"
               in
               exit 1)
        with
          true
        then
          1
        else
          ifCont5 left3 right3 0
in
let compAge: Event -> Event -> Int =
  lam left2: Event.
    lam right2: Event.
      match
        isNaN1
          (let target66 = right2 in
           match
             target66
           with
             Event1 x96
           then
             x96.eventTime
           else
             let #var"1" =
               print
                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 282:12-282:27>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mright.eventTime[0m[0m)) {\n"
             in
             exit 1)
      with
        true
      then
        negi 1
      else
        ifCont6 left2 right2 0
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
let anon35 =
  lam l1: Int.
    lam r2: Int.
      match
        eqi l1 r2
      with
        true
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
                       match
                         target26
                       with
                         EmbeddedMarkovChainMatrix1 x45
                       then
                         x45.totalRates
                       else
                         let #var"1" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 349:18-349:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                         in
                         exit 1)
                      (subi (addi startState 1) 1)
                  in
                  match
                    match
                      anon35 startState finalState1
                    with
                      true
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
                    let param2 =
                      get
                        (let target22 = embeddedQMatrix1 in
                         match
                           target22
                         with
                           EmbeddedMarkovChainMatrix1 x41
                         then
                           x41.transitionProbs
                         else
                           let #var"1" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 358:16-358:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[startState + 1];\n"
                           in
                           exit 1)
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
                             match
                               target20
                             with
                               HostBranchSample1 x39
                             then
                               x39.history
                             else
                               let #var"1" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 364:8-364:29>:\nField \'history\' not found\n[0m        [31mrestOfHistory.history[0m\n"
                               in
                               exit 1),
                        success =
                          let target21 = restOfHistory in
                          match
                            target21
                          with
                            HostBranchSample1 x40
                          then
                            x40.success
                          else
                            let #var"1" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 366:16-366:37>:\nField \'success\' not found\n[0m      success = [31mrestOfHistory.success[0m\n"
                            in
                            exit 1 }
                  else
                    let t2 = assume
                        (Exponential totalRate)
                    in
                    match
                      ltf (subf startAge t2) finalAge2
                    with
                      true
                    then
                      match
                        eqi startState finalState1
                      with
                        true
                      then
                        HostBranchSample1
                          { history = "", success = true }
                      else
                        HostBranchSample1
                          { history = "", success = false }
                    else
                      let nextState2 = sampleNextEvent startState embeddedQMatrix1 in
                      let param3 =
                        get
                          (let target25 = embeddedQMatrix1 in
                           match
                             target25
                           with
                             EmbeddedMarkovChainMatrix1 x44
                           then
                             x44.transitionProbs
                           else
                             let #var"1" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 390:18-390:49>:\nField \'transitionProbs\' not found\n[0m      let param = [31membeddedQMatrix.transitionProbs[0m[0m[startState + 1];\n"
                             in
                             exit 1)
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
                               match
                                 target23
                               with
                                 HostBranchSample1 x42
                               then
                                 x42.history
                               else
                                 let #var"1" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 399:10-399:31>:\nField \'history\' not found\n[0m          [31mrestOfHistory.history[0m\n"
                                 in
                                 exit 1),
                          success =
                            let target24 = restOfHistory1 in
                            match
                              target24
                            with
                              HostBranchSample1 x43
                            then
                              x43.success
                            else
                              let #var"1" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 401:18-401:39>:\nField \'success\' not found\n[0m        success = [31mrestOfHistory.success[0m\n"
                              in
                              exit 1 }
in
recursive
  let sampleUnorderedBranch: [Int] -> [Int] -> Float -> Float -> Int -> Int -> EmbeddedMarkovChainMatrix -> Int -> BranchSample =
    lam startRep: [Int].
      lam finalRep1: [Int].
        lam startAge1: Float.
          lam finalAge3: Float.
            lam hostIndex: Int.
              lam nhosts6: Int.
                lam embeddedQMatrix2: EmbeddedMarkovChainMatrix.
                  lam rejectionDepth: Int.
                    let _MAX_REJECTION_DEPTH_HOST = 100 in
                    match
                      leqi hostIndex nhosts6
                    with
                      true
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
                        match
                          target27
                        with
                          HostBranchSample1 x46
                        then
                          x46.success
                        else
                          let #var"1" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 311:7-311:26>:\nField \'success\' not found\n[0m    if [31mhostHistory.success[0m[0m {\n"
                          in
                          exit 1
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
                            nhosts6
                            embeddedQMatrix2
                            0
                        in
                        BranchSample1
                          { history =
                              cons1
                                (let target28 = hostHistory in
                                 match
                                   target28
                                 with
                                   HostBranchSample1 x47
                                 then
                                   x47.history
                                 else
                                   let #var"1" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 316:23-316:42>:\nField \'history\' not found\n[0m        history = cons([31mhostHistory.history[0m[0m, otherHostHistories.history),\n"
                                   in
                                   exit 1)
                                (let target29 = otherHostHistories in
                                 match
                                   target29
                                 with
                                   BranchSample1 x48
                                 then
                                   x48.history
                                 else
                                   let #var"1" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 316:44-316:70>:\nField \'history\' not found\n[0m        history = cons(hostHistory.history, [31motherHostHistories.history[0m[0m),\n"
                                   in
                                   exit 1),
                            success =
                              let target30 = otherHostHistories in
                              match
                                target30
                              with
                                BranchSample1 x49
                              then
                                x49.success
                              else
                                let #var"1" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 317:18-317:44>:\nField \'success\' not found\n[0m        success = [31motherHostHistories.success[0m\n"
                                in
                                exit 1 }
                      else match
                        leqi rejectionDepth _MAX_REJECTION_DEPTH_HOST
                      with
                        true
                      then
                        sampleUnorderedBranch
                          startRep
                          finalRep1
                          startAge1
                          finalAge3
                          hostIndex
                          nhosts6
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
  let sampleBranch: [Int] -> [Int] -> Float -> Float -> Int -> ModelParams -> Matrix Float -> Int -> CorrectedBranchSample =
    lam startRep1: [Int].
      lam finalRep2: [Int].
        lam startAge2: Float.
          lam finalAge4: Float.
            lam nhosts7: Int.
              lam modelParams1: ModelParams.
                lam branchKernel: Matrix Float.
                  lam rejectionDepth1: Int.
                    let _MAX_REJECTION_DEPTH_BRANCH = 100 in
                    match
                      leqi rejectionDepth1 _MAX_REJECTION_DEPTH_BRANCH
                    with
                      true
                    then
                      let unorderedBranch =
                        sampleUnorderedBranch
                          startRep1
                          finalRep2
                          startAge2
                          finalAge4
                          1
                          nhosts7
                          (let target34 = modelParams1 in
                           match
                             target34
                           with
                             ModelParams1 x53
                           then
                             x53.embeddedQMatrix
                           else
                             let #var"1" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 227:57-227:84>:\nField \'embeddedQMatrix\' not found\n[0m      startRep, finalRep, startAge, finalAge, 1, nhosts, [31mmodelParams.embeddedQMatrix[0m[0m, 1\n"
                             in
                             exit 1)
                          1
                      in
                      match
                        let target31 = unorderedBranch in
                        match
                          target31
                        with
                          BranchSample1 x50
                        then
                          x50.success
                        else
                          let #var"1" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 229:7-229:30>:\nField \'success\' not found\n[0m    if [31munorderedBranch.success[0m[0m {\n"
                          in
                          exit 1
                      with
                        true
                      then
                        let allHostEvents =
                          paste0
                            (let target33 = unorderedBranch in
                             match
                               target33
                             with
                               BranchSample1 x52
                             then
                               x52.history
                             else
                               let #var"1" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 233:33-233:56>:\nField \'history\' not found\n[0m      let allHostEvents = paste0([31munorderedBranch.history[0m[0m);\n"
                               in
                               exit 1)
                        in
                        let orderedEvents = qSort compAge allHostEvents in
                        let nEvents4 = length1 orderedEvents in
                        match
                          allTimesValidBranch startRep1 orderedEvents 1 nEvents4 nhosts7
                        with
                          true
                        then
                          let logDebt =
                            independenceLikelihoodEndCond
                              startRep1
                              finalRep2
                              startAge2
                              finalAge4
                              (let target32 = unorderedBranch in
                               match
                                 target32
                               with
                                 BranchSample1 x51
                               then
                                 x51.history
                               else
                                 let #var"1" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 243:50-243:73>:\nField \'history\' not found\n[0m          startRep, finalRep, startAge, finalAge, [31munorderedBranch.history[0m[0m, modelParams, branchKernel\n"
                                 in
                                 exit 1)
                              modelParams1
                              branchKernel
                          in
                          let logExcess =
                            fullModelWeight
                              1
                              startRep1
                              finalRep2
                              startAge2
                              finalAge4
                              orderedEvents
                              nEvents4
                              nhosts7
                              modelParams1
                          in
                          CorrectedBranchSample1
                            { history = orderedEvents,
                              success = true,
                              logDebt = logDebt,
                              logExcess = logExcess }
                        else
                          ifCont7
                            startRep1
                            finalRep2
                            startAge2
                            finalAge4
                            nhosts7
                            modelParams1
                            branchKernel
                            rejectionDepth1
                            0
                      else
                        ifCont8
                          startRep1
                          finalRep2
                          startAge2
                          finalAge4
                          nhosts7
                          modelParams1
                          branchKernel
                          rejectionDepth1
                          0
                    else
                      CorrectedBranchSample1
                        { history = "",
                          success = false,
                          logDebt = negf (log1 0.),
                          logExcess = log1 0. }
  let ifCont8 =
    lam startRep2.
      lam finalRep3.
        lam startAge3.
          lam finalAge5.
            lam nhosts8.
              lam modelParams2.
                lam branchKernel1.
                  lam rejectionDepth2.
                    lam #var"4": Int.
                      sampleBranch
                        startRep2
                        finalRep3
                        startAge3
                        finalAge5
                        nhosts8
                        modelParams2
                        branchKernel1
                        (addi rejectionDepth2 1)
  let ifCont7 =
    lam startRep3.
      lam finalRep4.
        lam startAge4.
          lam finalAge6.
            lam nhosts9.
              lam modelParams3.
                lam branchKernel2.
                  lam rejectionDepth3.
                    lam #var"5": Int.
                      ifCont8
                        startRep3
                        finalRep4
                        startAge4
                        finalAge6
                        nhosts9
                        modelParams3
                        branchKernel2
                        rejectionDepth3
                        0
in
recursive
  let ifCont9 =
    lam tree2.
      lam nhosts10.
        lam modelParams4.
          lam rep1.
            lam branchSample.
              lam #var"6": Int.
                let newMsg = mtxCreate nhosts10 3 (observationMessage rep1 1 nhosts10)
                in
                let leftMsg =
                  mtxMul
                    newMsg
                    (let target45 = tree2 in
                     match
                       target45
                     with
                       MsgNode x68
                     then
                       x68.leftKernel
                     else
                       let #var"1" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 191:33-191:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n"
                       in
                       exit 1)
                in
                let rightMsg =
                  mtxMul
                    newMsg
                    (let target44 = tree2 in
                     match
                       target44
                     with
                       MsgNode x67
                     then
                       x67.rightKernel
                     else
                       let #var"1" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 192:34-192:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n"
                       in
                       exit 1)
                in
                let left1 =
                  sampleTreeHistory
                    (let target41 = tree2 in
                     match
                       target41
                     with
                       MsgNode x63
                     then
                       x63.left
                     else
                       let #var"1" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 196:6-196:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nhosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n"
                       in
                       exit 1)
                    nhosts10
                    leftMsg
                    rep1
                    (let target42 = tree2 in
                     match
                       target42
                     with
                       MsgNode x64
                     then
                       x64.age
                     else match
                       target42
                     with
                       MsgLeaf x65
                     then
                       x65.age
                     else
                       let #var"1" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 196:39-196:47>:\nField \'age\' not found\n[0m      tree.left, nhosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n"
                       in
                       exit 1)
                    modelParams4
                    (let target43 = tree2 in
                     match
                       target43
                     with
                       MsgNode x66
                     then
                       x66.leftKernel
                     else
                       let #var"1" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 196:62-196:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nhosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n"
                       in
                       exit 1)
                in
                let right1 =
                  sampleTreeHistory
                    (let target38 = tree2 in
                     match
                       target38
                     with
                       MsgNode x59
                     then
                       x59.right
                     else
                       let #var"1" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 199:6-199:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nhosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n"
                       in
                       exit 1)
                    nhosts10
                    rightMsg
                    rep1
                    (let target39 = tree2 in
                     match
                       target39
                     with
                       MsgNode x60
                     then
                       x60.age
                     else match
                       target39
                     with
                       MsgLeaf x61
                     then
                       x61.age
                     else
                       let #var"1" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 199:41-199:49>:\nField \'age\' not found\n[0m      tree.right, nhosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n"
                       in
                       exit 1)
                    modelParams4
                    (let target40 = tree2 in
                     match
                       target40
                     with
                       MsgNode x62
                     then
                       x62.rightKernel
                     else
                       let #var"1" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 199:64-199:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nhosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n"
                       in
                       exit 1)
                in
                HistoryNode
                  { age =
                      let target35 = tree2 in
                      match
                        target35
                      with
                        MsgNode x54
                      then
                        x54.age
                      else match
                        target35
                      with
                        MsgLeaf x55
                      then
                        x55.age
                      else
                        let #var"1" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 203:12-203:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
                        in
                        exit 1,
                    left = left1,
                    right = right1,
                    label =
                      let target36 = tree2 in
                      match
                        target36
                      with
                        MsgNode x56
                      then
                        x56.label
                      else match
                        target36
                      with
                        MsgLeaf x57
                      then
                        x57.label
                      else
                        let #var"1" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 204:14-204:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                        in
                        exit 1,
                    repertoire = rep1,
                    history =
                      let target37 = branchSample in
                      match
                        target37
                      with
                        CorrectedBranchSample1 x58
                      then
                        x58.history
                      else
                        let #var"1" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 206:16-206:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n"
                        in
                        exit 1 }
  let sampleTreeHistory: MsgTree -> Int -> Matrix Float -> [Int] -> Float -> ModelParams -> Matrix Float -> HistoryTree =
    lam tree3: MsgTree.
      lam nhosts11: Int.
        lam preorderMsg: Matrix Float.
          lam parentRep: [Int].
            lam parentAge: Float.
              lam modelParams5: ModelParams.
                lam branchKernel3: Matrix Float.
                  match
                    match
                      tree3
                    with
                      MsgLeaf _
                    then
                      true
                    else
                      false
                  with
                    true
                  then
                    let rep2 =
                      let target50 = tree3 in
                      match
                        target50
                      with
                        MsgLeaf x74
                      then
                        x74.interactions
                      else
                        let #var"1" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 136:14-136:31>:\nField \'interactions\' not found\n[0m    let rep = [31mtree.interactions[0m[0m;\n"
                        in
                        exit 1
                    in
                    let branchSample1 =
                      sampleBranch
                        parentRep
                        rep2
                        parentAge
                        (let target49 = tree3 in
                         match
                           target49
                         with
                           MsgNode x72
                         then
                           x72.age
                         else match
                           target49
                         with
                           MsgLeaf x73
                         then
                           x73.age
                         else
                           let #var"1" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 142:6-142:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                           in
                           exit 1)
                        nhosts11
                        modelParams5
                        branchKernel3
                        0
                    in
                    match
                      let target46 = branchSample1 in
                      match
                        target46
                      with
                        CorrectedBranchSample1 x69
                      then
                        x69.success
                      else
                        let #var"1" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 150:7-150:27>:\nField \'success\' not found\n[0m    if [31mbranchSample.success[0m[0m {\n"
                        in
                        exit 1
                    with
                      true
                    then
                      let foo1 =
                        weight
                          (subf
                             (let target47 = branchSample1 in
                              match
                                target47
                              with
                                CorrectedBranchSample1 x70
                              then
                                x70.logExcess
                              else
                                let #var"1" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 151:16-151:38>:\nField \'logExcess\' not found\n[0m      logWeight [31mbranchSample.logExcess[0m[0m - branchSample.logDebt;\n"
                                in
                                exit 1)
                             (let target48 = branchSample1 in
                              match
                                target48
                              with
                                CorrectedBranchSample1 x71
                              then
                                x71.logDebt
                              else
                                let #var"1" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 151:41-151:61>:\nField \'logDebt\' not found\n[0m      logWeight branchSample.logExcess - [31mbranchSample.logDebt[0m[0m;\n"
                                in
                                exit 1))
                      in
                      ifCont4 tree3 rep2 branchSample1 0
                    else
                      let foo2 = weight
                          (externalLog 0.) in
                      ifCont4 tree3 rep2 branchSample1 0
                  else
                    let samplingProb =
                      mtxElemMul
                        (let target55 = tree3 in
                         match
                           target55
                         with
                           MsgNode x80
                         then
                           x80.outMsg
                         else match
                           target55
                         with
                           MsgLeaf x81
                         then
                           x81.outMsg
                         else
                           let #var"1" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 164:34-164:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n"
                           in
                           exit 1)
                        preorderMsg
                    in
                    let initRep = suggestRepAligned samplingProb 1 nhosts11 in
                    let rep3 = suggestRepRS samplingProb nhosts11 initRep 0 in
                    let nodeLogDebt = getRepertoireDebt rep3 samplingProb nhosts11
                    in
                    let branchSample2 =
                      sampleBranch
                        parentRep
                        rep3
                        parentAge
                        (let target54 = tree3 in
                         match
                           target54
                         with
                           MsgNode x78
                         then
                           x78.age
                         else match
                           target54
                         with
                           MsgLeaf x79
                         then
                           x79.age
                         else
                           let #var"1" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 174:6-174:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                           in
                           exit 1)
                        nhosts11
                        modelParams5
                        branchKernel3
                        0
                    in
                    match
                      let target51 = branchSample2 in
                      match
                        target51
                      with
                        CorrectedBranchSample1 x75
                      then
                        x75.success
                      else
                        let #var"1" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 182:7-182:27>:\nField \'success\' not found\n[0m    if [31mbranchSample.success[0m[0m {\n"
                        in
                        exit 1
                    with
                      true
                    then
                      let foo3 =
                        weight
                          (subf
                             (subf
                                (let target52 = branchSample2 in
                                 match
                                   target52
                                 with
                                   CorrectedBranchSample1 x76
                                 then
                                   x76.logExcess
                                 else
                                   let #var"1" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 183:16-183:38>:\nField \'logExcess\' not found\n[0m      logWeight [31mbranchSample.logExcess[0m[0m - branchSample.logDebt - nodeLogDebt;\n"
                                   in
                                   exit 1)
                                (let target53 = branchSample2 in
                                 match
                                   target53
                                 with
                                   CorrectedBranchSample1 x77
                                 then
                                   x77.logDebt
                                 else
                                   let #var"1" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 183:41-183:61>:\nField \'logDebt\' not found\n[0m      logWeight branchSample.logExcess - [31mbranchSample.logDebt[0m[0m - nodeLogDebt;\n"
                                   in
                                   exit 1))
                             nodeLogDebt)
                      in
                      ifCont9 tree3 nhosts11 modelParams5 rep3 branchSample2 0
                    else
                      let foo4 = weight
                          (externalLog 0.) in
                      ifCont9 tree3 nhosts11 modelParams5 rep3 branchSample2 0
in
let anon36: [Float] -> Dist([Float]) = lam lambda1.
    rbLambdaMove lambda1
in
let anon37: Float -> Dist(Float) = lam mu1.
    rbMuMove mu1 in
let anon38: Float -> Dist(Float) = lam beta1.
    rbBetaMove beta1
in
let rejectAccept: TreeLabeled -> Int -> Int -> [Int] -> [Float] -> Float -> ReturnType =
  lam symbiont_tree: TreeLabeled.
    lam ntips: Int.
      lam nhosts12: Int.
        lam interactions2: [Int].
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
              let qMatrix2 = mtxSclrMul mu r1 in
              let nestedInteractions = nestSeq interactions2 ntips nhosts12
              in
              let postorderTree =
                postorderTraverse symbiont_tree qMatrix2 nestedInteractions nhosts12
              in
              let rootPrior = mtxCreate nhosts12 3 (ones (muli 3 nhosts12))
              in
              let rootSamplingProb =
                mtxElemMul
                  (let target65 = postorderTree in
                   match
                     target65
                   with
                     MsgNode x94
                   then
                     x94.outMsg
                   else match
                     target65
                   with
                     MsgLeaf x95
                   then
                     x95.outMsg
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 41:36-41:56>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31mpostorderTree.outMsg[0m[0m, rootPrior);\n"
                     in
                     exit 1)
                  rootPrior
              in
              let initRootRep = suggestRepAligned rootSamplingProb 1 nhosts12
              in
              let rootRep = suggestRepRS rootSamplingProb nhosts12 initRootRep 0
              in
              let rootLogDebt = getRepertoireDebt rootRep rootSamplingProb nhosts12
              in
              let rootLogExcess =
                negf
                  (log1
                     (subf (pow 3. (int2float nhosts12)) (pow 2. (int2float nhosts12))))
              in
              let foo5 = weight
                  (subf rootLogExcess rootLogDebt)
              in
              let newMsg1 = mtxCreate nhosts12 3 (observationMessage rootRep 1 nhosts12)
              in
              let leftMsg1 =
                mtxMul
                  newMsg1
                  (let target64 = postorderTree in
                   match
                     target64
                   with
                     MsgNode x93
                   then
                     x93.leftKernel
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 54:31-54:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n"
                     in
                     exit 1)
              in
              let rightMsg1 =
                mtxMul
                  newMsg1
                  (let target63 = postorderTree in
                   match
                     target63
                   with
                     MsgNode x92
                   then
                     x92.rightKernel
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 55:32-55:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n"
                     in
                     exit 1)
              in
              let embeddedQMatrix3 = rateMatrixToEmbeddedMarkovChain qMatrix2
              in
              let modelParams6 =
                ModelParams1
                  { beta = beta,
                    hostMetric = mtxCreate nhosts12 nhosts12 host_distances,
                    embeddedQMatrix = embeddedQMatrix3,
                    meanDist = dMean }
              in
              let rootAge =
                let target62 = postorderTree in
                match
                  target62
                with
                  MsgNode x90
                then
                  x90.age
                else match
                  target62
                with
                  MsgLeaf x91
                then
                  x91.age
                else
                  let #var"1" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 67:16-67:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
                  in
                  exit 1
              in
              let leftRepertoireTree =
                sampleTreeHistory
                  (let target60 = postorderTree in
                   match
                     target60
                   with
                     MsgNode x88
                   then
                     x88.left
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 69:4-69:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nhosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n"
                     in
                     exit 1)
                  nhosts12
                  leftMsg1
                  rootRep
                  rootAge
                  modelParams6
                  (let target61 = postorderTree in
                   match
                     target61
                   with
                     MsgNode x89
                   then
                     x89.leftKernel
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 69:72-69:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nhosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n"
                     in
                     exit 1)
              in
              let rightRepertoireTree =
                sampleTreeHistory
                  (let target58 = postorderTree in
                   match
                     target58
                   with
                     MsgNode x86
                   then
                     x86.right
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 72:4-72:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nhosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n"
                     in
                     exit 1)
                  nhosts12
                  rightMsg1
                  rootRep
                  rootAge
                  modelParams6
                  (let target59 = postorderTree in
                   match
                     target59
                   with
                     MsgNode x87
                   then
                     x87.rightKernel
                   else
                     let #var"1" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 72:74-72:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nhosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n"
                     in
                     exit 1)
              in
              let historyTree =
                HistoryNode
                  { age =
                      let target56 = symbiont_tree in
                      match
                        target56
                      with
                        Node x82
                      then
                        x82.age
                      else match
                        target56
                      with
                        Leaf x83
                      then
                        x83.age
                      else
                        let #var"1" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 77:10-77:27>:\nField \'age\' not found\n[0m    age = [31msymbiont_tree.age[0m[0m, label = symbiont_tree.label,\n"
                        in
                        exit 1,
                    left = leftRepertoireTree,
                    right = rightRepertoireTree,
                    label =
                      let target57 = symbiont_tree in
                      match
                        target57
                      with
                        Node x84
                      then
                        x84.label
                      else match
                        target57
                      with
                        Leaf x85
                      then
                        x85.label
                      else
                        let #var"1" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 77:37-77:56>:\nField \'label\' not found\n[0m    age = symbiont_tree.age, label = [31msymbiont_tree.label[0m[0m,\n"
                        in
                        exit 1,
                    repertoire = rootRep,
                    history = "" }
              in
              ReturnType1
                { lambda = lambda, mu = mu, beta = beta, tree = historyTree }
in
let anon39: {dMean: Float, ntips: Int, nhosts: Int, interactions: [Int], symbiont_tree: TreeLabeled, host_distances: [Float]} -> () -> ReturnType =
  lam input1.
    lam #var"7".
      rejectAccept
        input1.symbiont_tree
        input1.ntips
        input1.nhosts
        input1.interactions
        input1.host_distances
        input1.dMean
in
let input = { symbiont_tree = Leaf { label = 1, age = 0.0 }, ntips = 1, nhosts = 1, interactions = [1], host_distances = [1.], dMean = 1.} in
let tmp = anon39 input {} in
dprint tmp
