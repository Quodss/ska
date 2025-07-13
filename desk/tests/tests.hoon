/+  *test, *skan,  playpen, hoot
::
=/  expect-eq-nock
  |=  [sub=* fol=*]
  (expect-eq !>((mole |.(.*(sub fol)))) !>((run-nomm sub fol)))
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
  (expect-eq-nock cor fol)
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
  (expect-eq-nock cor fol)
::
++  test-scow-playpen
  =/  cor  ..scow:playpen
  =/  fol
    =>  cor  !=
    (scow %ud 5)
  ::
  (expect-eq-nock cor fol)
::
++  test-scow-hoot
  =/  cor  ..scow:hoot
  =/  fol
    =>  cor  !=
    (scow %ud 5)
  ::
  (expect-eq-nock cor fol)
::
++  test-parser
  =/  cor
    =>  ..ride:hoot
    |%
    ++  test  (expr-parse "3+3+4+1+2")
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
  (expect-eq-nock cor fol)
--