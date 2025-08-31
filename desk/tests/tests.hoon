/+  *test, *skan,  playpen, hoot
::
=/  expect-eq-nock-need
  |=  [sub=* fol=*]
  ^-  tang
  ?~  mol=(mole |.(.*(sub fol)))
    ~[leaf+"bad test"]
  (expect-eq !>(mol) !>((run-nomm sub fol)))
::
|%
++  test-once-dabl
  =/  cor
    =>  ~
    !:
    |.
    =/  once  |=(@ +(+<))
    =/  dabl  =>  +  |=(@ +(+(+<)))
    =/  slam  |=(g=$-(@ @) |=(n=@ (g n)))
    [((slam once) 1) ((slam dabl) 1)]
  ::
  =/  fol  [9 2 0 1]
  (expect-eq-nock-need cor fol)
::
++  test-dec
  =/  cor
    !:
    =>  ~
    |.
    %.  3
    |=  n=@
    ^-  @
    ?<  =(0 n)
    =/  c  0
    |-  ^-  @
    ?:  =(+(c) n)  c
    $(c +(c))
  ::
  =/  fol  [9 2 0 1]
  (expect-eq-nock-need cor fol)
::
++  test-scow-playpen
  =/  cor  ..scow:playpen
  =/  fol
    =>  cor  !=
    (scow %ud 5)
  ::
  (expect-eq-nock-need cor fol)
::
++  test-scow-hoot
  =/  cor  ..scow:hoot
  =/  fol
    =>  cor  !=
    (scow %ud 5)
  ::
  (expect-eq-nock-need cor fol)
::
++  test-parser
  =/  cor
    =>  ..ride:hoot
    |%
    ++  test  (expr-parse "33+3+4\\\0a/1+1+2")
    ++  expr-parse
      |=  math=tape
      (scan math expr)
      ::
    ++  expr
      %+  knee  *@ud
      |.  ~+
      ;~  pose
        ((slug add) lus ;~(pose dem expr))
        dem
      ==
    --
  ::
  =/  fol
    =>  cor  !=
    test
  ::
  (expect-eq-nock-need cor fol)
::
++  test-muk
  =/  cor  playpen
  =/  fol
    =>  cor  !=
    (muk 0xcafe.babe 1 42)  ::  XX 42 42 42 is a jet mismatch
  ::
  (expect-eq-nock-need cor fol)

++  test-y-comb
  =/  sub
    =>  ..add:hoot
    |%
    ++  y
      |*  [m1=mold m2=mold]
      |=  f=$-($-(m1 m2) $-(m1 m2))
      |=  x=m1
      ^-  m2
      ((f .) x)
    ::
    ++  fac-f
      |=  cont=$-(@ @)
      |=  x=@
      ^-  @
      ?:  =(x 0)  1
      (mul x (cont (dec x)))
    --
  ::
  =/  fol
    =>  sub  !=
    (((y @ @) fac-f) 5)
  ::
  (expect-eq-nock-need sub fol)
::
++  test-ream
  =/  cor  hoot
  =/  fol
    =>  cor  !=
    (ream '42')
  ::
  (expect-eq-nock-need cor fol)
--