/-  *noir
/+  skan
::
:-  %say  |=  *  :-  %noun
::
=/  fol  [9 2 0 1]  ::  0x0
=/  cor
  !.
  =>  ~
  |.
:: =/  once  |=(@ +(+<))
:: =/  dabl  =>  +  |=(@ +(+(+<)))
:: =/  slam  |=(g=$-(@ @) |=(n=@ (g n)))
:: [((slam once) 1) ((slam dabl) 1)]
%.  3
|=  n=@
^-  @
?<  =(0 n)
=/  c  0
|-  ^-  @
?:  =(+(c) n)  c
$(c +(c))
::
(run-nomm:skan cor fol)