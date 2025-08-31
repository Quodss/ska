/+  *skan
::
=/  cor  hoot
=/  fol
  =>  cor  !=
  (ream '42')
::
=/  gen
  ~>  %bout
  (scan &+cor fol)
::
=/  map-locals=(map @uxsite [less=sock fol=* =nomm])  (malt locals.gen)
=/  edit  (rewrite-memo (malt memo-loop-entry.gen))
=.  map-locals
  ~&  %map-locals-rewrite
  ~>  %bout
  %-  ~(run by map-locals)
  |=  [sock * =nomm]
  +<(nomm (edit nomm))
::
=.  idxs.memo.gen
  ~&  %memo-idxs-rewrite
  ~>  %bout
  %-  ~(run by idxs.memo.gen)
  |=  meme
  +<(code (edit code))
::
=.  sits.memo.gen
  ~&  %memo-sits-rewrite
  ~>  %bout
  %-  ~(run by sits.memo.gen)
  |=  meme
  +<(code (edit code))
::
=.  fols.memo.gen
  ~&  %memo-fols-rewrite
  ~>  %bout
  %-  ~(run by fols.memo.gen)
  |=  l=(list meme)
  %+  turn  l
  |=  meme
  +<(code (edit code))
::
[map-locals gen]