/+  skan
::
:-  %say  |=  *  :-  %noun
::
=/  fol  [9 2 0 1]  ::  0x0
=/  cor
  !.  ::  0x1
  =>  ~
  |.
  =/  once  |=(@ +(+<))
  =/  dabl  =>  +  |=(@ +(+(+<)))
  =/  slam  |=(g=$-(@ @) |=(n=@ (g n)))
  [((slam once) 1) ((slam dabl) 1)]
::
(run-nomm:skan cor fol)