/+  *soak
|%
::    Nomm (Nock--)
::
::  [%9 p q] => [%7 q %2 [%0 1] %0 p]
::  [%8 p q] => [%7 [p %0 1] q]  (assert p is a cell)
::
+$  nomm
  $^  [nomm nomm]                             ::  autocons
  $%  [%1 p=*]                                ::  Nock 1
  ::                                          ::  Nock 2
      [%f2 p=nomm func=@uxfunc]               ::    call function with compatible subject
      [%r2 p=nomm q=nomm site=@uxsite]        ::    raw Nock 2: not done or code object construction or indirect
      [%3 p=nomm]                             ::  Nock 3
      [%4 p=nomm]                             ::  Nock 4
      [%5 p=nomm q=nomm]                      ::  Nock 5
      [%6 p=nomm q=nomm r=nomm]               ::  Nock 6
      [%7 p=nomm q=nomm]                      ::  Nock 7
      [%10 p=[p=@ q=nomm] q=nomm]             ::  Nock 10
      [%s11 p=@ q=nomm]                       ::  Nock 11 (static)
      [%d11 p=[p=@ q=nomm] q=nomm]            ::  Nock 11 (dynamic)
      [%12 p=nomm q=nomm]                     ::  "Nock 12"
      [%0 p=@]                                ::  Nock 0
  ==
::  a call product is either used as code or not
::  if it is not used as code, it is associated with a function object
::  described with [sub=sock fol=*]
::
::  the result of analysis of outer call is assumed to not be used as code,
::  which needs to be reconsidered for +poke:arvo analysis
::
+$  functions
  $:
    ::  callsites <--> functions
    ::
    sites=(map @uxsite @uxfunc)
    calls=(jar @uxfunc @uxsite)
  ::::
    ::  Function definitions
    ::
    codes=(map @uxfunc nomm)
  ::::
    ::  functions <--> [sub=sock fol=*] XX not necessary?
    ::  can be built by composing mappings of evals with functions
    ::
    :: forms=(jar * [func=@uxfunc sub=sock])  ::  search by formula
    :: bells=(jar @uxfunc [sub=sock fol=*])   ::  search by function label
  ==
::  generic call info
::
+$  evals
  $:
    ::  evalsites <--> sub/fol pairs
    ::
    sites=(map @uxsite [sub=sock fol=*])
    calls=(jar * [site=@uxsite sub=sock])
  ==
::  provenance tree, BUT!!! axis of the RESULT of evalsite, not subject
::
+$  source  (tree (list (pair @axis @uxsite)))
+$  sock-source  [=sock =source]
--