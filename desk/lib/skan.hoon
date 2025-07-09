/-  *noir
/+  hoot
/+  playpen
::  TODO ~2025.7.4:
::    meloization
::    
=*  stub  !!
=*  one  `@`1
::  ignorant sock-anno
::
=/  dunno  [|+~ ~]
::  default flags: not loopy, fully direct
::
=/  deff  [| &]
=/  verb  &
=/  bars  &
::
|%
++  weld-meal
  |=  [* ls=[(list meal) (list meal)]]
  (weld ls)
::
++  scux  ^~((cury scot %ux))
::  print analysis stack
::
++  ps
  |=  [bars=@ud tag=cord comment=cord diff=@s]
  ^+  bars
  ?.  verb  bars
  ?.  ^bars  ((slog (rap 3 tag ' ' comment ~) ~) 0)
  =/  [bars-print=@ bars-return=@]
    ?+  diff  ~|(%weird-diff !!)
      %--0  [bars bars]
      %--1  [. .]:(succ bars)
      %-1   [bars ~|(%bars-underrun (dec bars))]
    ==
  ::
  ((slog (rap 3 tag ' ' (fil 3 bars-print '|') ' ' comment ~) ~) bars-return)
::  redo blocklist parent -> children
::
+$  blocklist  (jug @uxsite @uxsite)
::  a formula is loopy if it is a Nock 2 that was estimated to be a loop or
::  if the formula contains a loopy formula.
::  if eval'd formula is loopy then it cannot be finalized unless it is
::  an entry point into a loop, in which case it is finalized by checking
::  the assumptions made when analyzing the call graph cycle. entry points
::  and assumptions are recorded in cycles.gen
::
::  invariant: if a formula is loopy then cycles.gen is not empty and its
::  first element is the cycle we are currently in
::
::  direct: fully direct, to avoid memoizing evals that are too generic,
::  otherwise more specific evals would not be reanalyzed
::
+$  flags  [loopy=? direct=?]
::  error: either m or parent-kid assumption pair which turned out to be false
::
++  error
  |$  [m]
  (each m (pair @uxsite @uxsite))
::
+$  err-state  (error state)
+$  frond  (deep [par=@uxsite kid=@uxsite par-sub=sock kid-sub=sock-anno])
+$  cycle
  $:  entry=@uxsite
      latch=@uxsite
      =frond
      set=(deep @uxsite)
      melo=(jar * meal)
  ==
::
++  add-frond
  |=  [new=[par=@uxsite kid=@uxsite sock sock-anno] cycles=(list cycle)]
  ^-  (list cycle)
  ?:  |(?=(~ cycles) (gth par.new latch.i.cycles))
    ::  push new cycle
    ::
    :_  cycles
    ^-  cycle
    [par.new kid.new [%list new ~] [%list ~[kid.new]] ~]
  ::  pop and extend top cycle
  ::
  =/  new-cycle=cycle
    :*  (min par.new entry.i.cycles)
        kid.new
        (dive frond.i.cycles new)
        (dive set.i.cycles kid.new)
        melo.i.cycles
    ==
  ::
  =/  rest  t.cycles
  ::
  |-  ^-  (list cycle)
  ?:  |(?=(~ rest) (gth entry.new-cycle latch.i.rest))
    ::  push extended cycle
    ::
    [new-cycle rest]
  ::  pop and merge overlapping cycle
  ::
  =.  entry.new-cycle  (min entry.new-cycle entry.i.rest)
  =.  frond.new-cycle  [%deep frond.new-cycle frond.i.rest]
  =.  set.new-cycle    [%deep set.new-cycle set.i.rest]
  =.  melo.new-cycle   ((~(uno by melo.new-cycle) melo.i.rest) weld-meal)
  ::
  $(rest t.rest)
::
+$  state
  ::  global state
  ::    results:  result table
  ::    site:     eval index generator
  ::    cycles:   stack of call graph cycles (aka natural loops aka strongly
  ::    connected components)
  ::      entry: top-most entry into a cyclical call graph
  ::      latch: right-most, bottom-most evalsite of the cycle
  ::      frond: set of parent-kid pairs of loop assumptions
  ::             (target of hypothetical backedge, target of the actual edge,
  ::              subject socks at the par/kid evalsites)
  ::      set: set of all vertices in the cycle (to delete from want.gen when
  ::           done)
  ::
  ::      When new assumptions are made, we either extend an old cycle, possibly
  ::      merging multiple predecessor cycles, or add a new one if its
  ::      finalization does not depend on previous cycles. Thus, when we finish
  ::      analysis of a site which is recorded as an entry in `cycles`, we only
  ::      have to check top cycle entry and we can finalize that loop
  ::      independently of loops deeper in the stack.
  ::
  ::      New cycle condition for a parent-kid pair:
  ::        parent > latch.i.-.cycles (compare site labels)
  ::      If false, extend top cycle (set latch to kid, entry to
  ::      min(entry, parent)), then iterate over the rest of the list, 
  ::      merging if new cycle overlaps with the predecessor
  ::      (new entry <= previous latch)
  ::
  ::    want: evalsite subject requirements of non-finalized evalsites:
  ::      parts of the subject that are used as code
  ::
  $:  =results
      site=@uxsite
      cycles=(list cycle)
      want=urge
      bars=@ud
  ==
::
+$  stack
  ::  TODO leave essential
  ::
  $:
    ::  list: linear stack of evalsites
    ::    
    list=(list (trel sock * @uxsite))
    ::  fols: search by formula
    ::
    fols=(jar * (pair sock-anno @uxsite))
    ::  set: set of evalsites on the stack
    ::
    set=(set @uxsite)
  ==
::
++  scan
  |=  [bus=* fol=*]  :: no autocons disassembly
  ^-  state
  =|  gen=state
  =|  =stack  ::  lexically scoped
  =/  sub=sock-anno  [&+bus ~]
  =;  res-eval
    ::  debug asserts
    ::
    ?>  =(~ cycles.gen.res-eval)
    ?.  =(~ want.gen.res-eval)
      ~|  ~(key by want.gen.res-eval)
      !!
    gen.res-eval
  =^  here-site  gen  [site.gen gen(site +(site.gen))]
  ?>  =(0x0 here-site)
  |-  ^-  [[sock-anno flags] gen=state]
  =*  eval-loop  $
  ::  retry evalsite analysis if a loop assumption was wrong
  ::
  =|  loop-block=blocklist
  |-  ^-  [[sock-anno flags] state]
  =*  redo-loop  $
  =;  res
    ?-  -.res
      %&  p.res
      %|  ~&  >>>  %redo
          redo-loop(loop-block (~(put ju loop-block) p.res))
    ==
  ^-  (error [[sock-anno flags] state])
  ::  record current evalsite in the subject provenance tree
  ::
  =.  src.sub
    ?~  src.sub  [[one here-site]~ ~ ~]
    src.sub(n [[one here-site] n.src.sub])
  ::  check memo cache
  ::
  ?^  m=(memo here-site fol sub gen set.stack)
    =.  bars.gen.u.m
      %:  ps  bars.gen  'memo:'
        (rap 3 (scux here-site) ' <- ' (scux from.u.m) ~)
        --0
      ==
    ::
    &+[[pro.u.m deff] gen.u.m]
  ::  check melo cache (melo hit makes call loopy, might merge some cycles)
  ::
  ?^  m=(melo here-site fol sub gen set.stack)
    =.  bars.gen.u.m
      %:  ps  bars.gen  'melo:'
        (rap 3 (scux here-site) ' <- ' (scux from.u.m) ~)
        --0
      ==
    ::
    &+[[pro.u.m [& &]] gen.u.m]
  ::
  ::  push on the stack
  ::
  =.  list.stack  [[sock.sub fol here-site] list.stack]
  =.  fols.stack  (~(add ja fols.stack) fol sub here-site)
  =.  set.stack   (~(put in set.stack) here-site)
  ::
  =^  [code=nomm prod=sock-anno =flags]  gen
    =.  bars.gen  (ps bars.gen 'step:' (rap 3 (scux here-site) ~) --1)
    |-  ^-  [[nomm sock-anno flags] state]
    =*  fol-loop  $
    ?+    fol  [[[%0 0] dunno deff] gen]
        [p=^ q=^]
      =^  [l-code=nomm l-prod=sock-anno l-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [r-code=nomm r-prod=sock-anno r-flags=flags]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [l-code r-code]
        :-  (~(knit so sock.l-prod) sock.r-prod)
        (cons:source src.l-prod src.r-prod)
      (fold-flag l-flags r-flags ~)
    ::
        [%0 p=@]
      ?:  =(0 p.fol)  [[fol dunno deff] gen]
      :_  gen
      :+  fol
        :-  (~(pull so sock.sub) p.fol)
        (slot:source src.sub p.fol)
      deff
    ::
        [%1 p=*]
      :_  gen
      [fol [&+p.fol ~] deff]
    ::
        [%2 p=^ q=^]
      =^  [s-code=nomm s-prod=sock-anno s-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [f-code=nomm f-prod=sock-anno f-flags=flags]  gen  fol-loop(fol q.fol)
      =^  there-site  gen  [site.gen gen(site +(site.gen))]
      ?.  =(& cape.sock.f-prod)
        ::  indirect call
        ::
        =.  bars.gen  (ps bars.gen 'indi:' (rap 3 (scux there-site) ~) --0)
        :_  gen
        :+  [%2 s-code f-code there-site]
          dunno
        (fold-flag s-flags f-flags [| |] ~)
      ::  direct call
      ::
      =/  fol-new  data.sock.f-prod
      =/  fol-urge  (urge:source (mask:source src.f-prod & `set.stack) &)
      =.  want.gen  (uni-urge:source want.gen fol-urge)
      ::
      ::  check for loop:
      ::    Check if there is formula in the stack above us that has a
      ::    quasi-compatible sock (heuristic), if yes we guess that this is
      ::    a loop and record both socks.
      ::
      ::    When finalizing, check that the differing parts of socks are not
      ::    used as code.
      ::
      ::    If they are, the guess was wrong, redo the analysis, putting
      ::    the parent-child pair in the blocklist
      ::
      ::  stack filtered by formula
      ::
      =/  tak  (~(get ja fols.stack) fol-new)
      |-  ^-  [[nomm sock-anno flags] state]
      =*  stack-loop  $
      ?^  tak
        ::  loop heuristic:
        ::  equal formulas, not in the blocklist, quasi matching subjects
        ::
        ?:  (~(has ju loop-block) q.i.tak there-site)
          stack-loop(tak t.tak)
        ?~  want=(close sock.s-prod sock.p.i.tak q.i.tak gen)
          stack-loop(tak t.tak)
        ::  loop hit
        ::
        ::  CAREFUL: ackchyually, here-site is the backedge root,
        ::  there-site/q.i.tak are the backedge targets that are assumed to be
        ::  the same (kid/parent) (but it should be totally fine to use kid as
        ::  latch, since we don't analyse through kid and all other calls that
        ::  would be greater than the latch would also be greater than the kid,
        ::  and vice versa)
        ::
        =.  bars.gen
          %:  ps  bars.gen  'loop:'
            (rap 3 (scux there-site) ' =?> ' (scux q.i.tak) ~)
            --0
          ==
        ::  propagate subject needs
        ::
        =.  src.s-prod  (mask:source src.s-prod cape.sock.s-prod `set.stack)
        =/  sub-urge  (urge:source src.s-prod u.want)
        =.  want.gen  (uni-urge:source want.gen sub-urge)
        =.  cycles.gen
          (add-frond [q.i.tak there-site sock.p.i.tak s-prod] cycles.gen)
        ::
        :_  gen
        :+  [%2 s-code f-code there-site]
          dunno
        (fold-flag s-flags f-flags [& &] ~)
      ::  non-loop case: analyse through
      ::
      =^  [pro=sock-anno =flags]  gen
        %=  eval-loop
          sub        s-prod
          fol        fol-new
          here-site  there-site
        ==
      :_  gen
      :+  [%2 s-code f-code there-site]
        pro
      (fold-flag flags s-flags f-flags ~)
    ::
        [%3 p=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      :_  gen
      :+  [%3 p-code]
        dunno
      p-flags
    ::
        [%4 p=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      :_  gen
      :+  [%4 p-code]
        dunno
      p-flags
    ::
        [%5 p=^ q=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [q-code=nomm * q-flags=flags]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [%5 p-code q-code]
        dunno
      (fold-flag p-flags q-flags ~)
    ::
        [%6 c=^ y=^ n=^]
      =^  [c-code=nomm * c-flags=flags]                 gen  fol-loop(fol c.fol)
      =^  [y-code=nomm y-prod=sock-anno y-flags=flags]  gen  fol-loop(fol y.fol)
      =^  [n-code=nomm n-prod=sock-anno n-flags=flags]  gen  fol-loop(fol n.fol)
      :_  gen
      ::  any of yes/no branches' code could be used, this is why we 
      ::  unionize the provenance trees
      ::
      =/  uni-source  (uni:source src.y-prod src.n-prod)
      ::  product sock is an intersection
      ::
      =/  int-sock  (~(purr so sock.y-prod) sock.n-prod)
      :+  [%6 c-code y-code n-code]
        :-  int-sock
        ::  mask unified provenance tree with intersection cape
        ::
        (mask:source uni-source cape.int-sock `set.stack)
      (fold-flag c-flags y-flags n-flags ~)
    ::
        [%7 p=^ q=^]
      =^  [p-code=nomm p-prod=sock-anno p-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [q-code=nomm q-prod=sock-anno q-flags=flags]  gen
        fol-loop(fol q.fol, sub p-prod)
      ::
      :_  gen
      :+  [%7 p-code q-code]
        q-prod
      (fold-flag p-flags q-flags ~)
    ::
        [%8 p=^ q=^]
      fol-loop(fol [%7 [p.fol %0 1] q.fol])
    ::
        [%9 p=@ q=^]
      fol-loop(fol [%7 q.fol %2 [%0 1] %0 p.fol])
    ::
        [%10 [a=@ don=^] rec=^]
      ?:  =(0 a.fol)  [[[%0 0] dunno [| &]] gen]
      =^  [don-code=nomm don-prod=sock-anno don-flags=flags]  gen
        fol-loop(fol don.fol)
      ::
      =^  [rec-code=nomm rec-prod=sock-anno rec-flags=flags]  gen
        fol-loop(fol rec.fol)
      ::
      :_  gen
      :+  [%10 [a.fol don-code] rec-code]
        :-  (~(darn so sock.rec-prod) a.fol sock.don-prod)
        (edit:source src.rec-prod a.fol src.don-prod)
      (fold-flag rec-flags don-flags ~)
    ::
        [%11 p=@ q=^]
      =^  [q-code=nomm q-prod=sock-anno q-flags=flags]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [%s11 p.fol q-code]
        q-prod
      q-flags
    ::
        [%11 [a=@ h=^] f=^]
      ::
      =^  [f-code=nomm f-prod=sock-anno f-flags=flags]  gen  fol-loop(fol f.fol)
      =^  [h-code=nomm h-prod=sock-anno h-flags=flags]  gen  fol-loop(fol h.fol)
      :_  gen
      :+  [%d11 [a.fol h-code] f-code]
        f-prod
      (fold-flag f-flags h-flags ~)
    ::
        [%12 p=^ q=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [q-code=nomm * q-flags=flags]  gen  fol-loop(fol q.fol)
      [[[%12 p-code q-code] dunno (fold-flag p-flags q-flags ~)] gen]
    ==
  ::  prune provenance tree to leave only calls on the stack (ourselves
  ::  included), removing cousin provenance; also mask down to the product cape
  ::
  =.  src.prod  (mask:source src.prod cape.sock.prod `set.stack)
  ::  make minimized subject
  ::
  ::  parts of the subject that are used as code downstream
  ::
  =/  want-site=cape  (~(gut by want.gen) here-site |)
  ::  minified subject sock for code: only code usage
  ::
  =/  less-code=sock  (~(app ca want-site) sock.sub)
  ::  we start off with more knowledge in the subject and mask down, 
  ::  so the intersection of want-site and cape.sock.sub should be exactly
  ::  equal to want-site?
  ::
  ?.  =(want-site cape.less-code)
    ~_  'cape.less-code < want-site'
    ~|  [cape.less-code want-site]
    !!
  ::  minified subject sock for memo: stricter requirement i.e. bigger sock,
  ::  includes possible subject captures
  ::
  ::  memoize only if fully direct
  ::
  =/  less-memo=(trap (unit sock))
    |.
    ?.  direct.flags  ~
    :-  ~
    ::  parts of subject that may have been captured by the result and thus
    ::  could be used as code by cousin evalsites
    ::
    =/  capture-res=cape
      (~(gut by (urge:source src.prod cape.sock.prod)) here-site |)
    ::
    =/  mask=cape  (~(uni ca want-site) capture-res)
    =/  less  (~(app ca mask) sock.sub)
    ?.  =(mask cape.less)
      ~_  'cape.less < mask'
      ~|  [cape.less mask]
      !!
    less
  ::
  ::  save results
  ::
  =.  every.results.gen  (~(put by every.results.gen) here-site less-code code)
  ::  if finalized: update loopiness (caller is not loopy due to a call to
  ::  a finalized entry into a cycle)
  ::
  =;  fin=(error [loopy=? gen=state])
    ?:  ?=(%| -.fin)  fin
    &+[[prod flags(loopy loopy.p.fin)] gen.p.fin]
  ?.  loopy.flags
    ::  success, non-loopy
    ::
    :+  %&  %|
    %:  final-simple
      here-site
      fol
      code
      $:less-memo
      less-code
      prod
      gen
    ==
  =*  i  ,.-.cycles.gen
  ?.  =(here-site entry.i)
    &+[& (process here-site sock.sub fol code prod gen direct.flags)]
  ::  cycle entry not loopy if finalized
  ::
  =-  ?:  ?=(%| -<)  -  &+[| p]
  ^-  err-state
  %:  final-cycle
    here-site
    fol
    code
    less-code
    $:less-memo
    prod
    gen
  ==
::  finalize analysis of non-loopy formula
::
++  final-simple
  |=  $:  site=@uxsite
          fol=*
          code=nomm
          less-memo=(unit sock)
          less-code=sock
          prod=sock-anno
          gen=state
      ==
  ^-  state
  =.  bars.gen  (ps bars.gen 'done:' (scux site) -1)
  =/  mayb-site=(unit cape)  (~(get by want.gen) site)
  =?  memo.results.gen  ?=(^ less-memo)
    %+  ~(add ja memo.results.gen)  fol
    :*  site
        code
        ::  minimized subjects' socks for memo checks and code checks
        ::
        u.less-memo
        less-code
        ::  full result, captured subject was included in memo requirement
        ::
        prod
    ==
  ::
  =?  want.gen  ?=(^ mayb-site)  (~(del by want.gen) site)
  gen
::  finalize analysis of a call graph cycle entry: pop cycle, verify assumptions
::
++  final-cycle
  |=  $:  site=@uxsite
          fol=*
          code=nomm
          less-code=sock
          less-memo=(unit sock)
          prod=sock-anno
          gen=state
      ==
  ^-  err-state
  =^  pop=cycle  cycles.gen  ?~(cycles.gen !! cycles.gen)
  =/  err-gen=err-state
    %+  roll-deep  frond.pop
    |:  :-  *[par=@uxsite kid=@uxsite par-sub=sock kid-sub=sock-anno]
        err-gen=`err-state`&+gen
    ^-  err-state
    ?:  ?=(%| -.err-gen)  err-gen
    =/  gen  p.err-gen
    =^  par-final=cape  gen
      =/  par-want-1=cape  (~(gut by want.gen) par |)
      |-  ^-  [cape state]
      =/  kid-sub-urge  (urge:source src.kid-sub par-want-1)
      =.  want.gen  (uni-urge:source want.gen kid-sub-urge)
      =/  par-want-2=cape  (~(gut by want.gen) par |)
      ?.  =(par-want-1 par-want-2)
        ~&  >>  %fixpoint-loop
        $(par-want-1 par-want-2)
      [par-want-1 gen]
    ::
    =/  par-want=cape  (~(gut by want.gen) par |)
    =/  par-masked=sock  (~(app ca par-final) par-sub)
    ?.  (~(huge so par-masked) sock.kid-sub)  ::  |+[par kid]
      ~|  [par kid]
      ~|  par-final
      !!
    =.  every.results.gen
      %+  ~(put by every.results.gen)  kid
      ?:  =(par site)  [less-code code]
      (~(got by every.results.gen) par)
    ::
    &+gen
  ::
  ?:  ?=(%| -.err-gen)  err-gen
  =.  gen  p.err-gen
  ::  remove err-gen
  ::
  =>  +
  =.  bars.gen  (ps bars.gen 'fini:' (scux site) -1)
  =.  want.gen  (~(del by want.gen) site)
  =.  want.gen
    %+  roll-deep  set.pop
    |:  [v=*@uxsite acc=want.gen]
    (~(del by acc) v)
  ::
  =?  memo.results.gen  ?=(^ less-memo)
    %+  ~(add ja memo.results.gen)  fol
    :*  site
        code
        u.less-memo
        less-code
        prod
    ==
  ::
  &+gen
::  treat analysis result of a non-finalized evalsite
::
++  process
  |=  [site=@uxsite sub=sock fol=* code=nomm prod=sock-anno gen=state direct=?]
  ^-  state
  =.  bars.gen  (ps bars.gen 'ciao:' (scux site) -1)
  ?~  cycles.gen  !!
  =.  set.i.cycles.gen   (dive set.i.cycles.gen site)
  =?  melo.i.cycles.gen  direct
    =/  capture-res=cape
      (~(gut by (urge:source src.prod cape.sock.prod)) site |)
    ::
    %+  ~(add ja melo.i.cycles.gen)  fol
    :*  site
        code
        capture-res
        sub
        prod
    ==
  ::
  gen
::
++  memo
  |=  [site=@uxsite fol=* sub=sock-anno gen=state stack=(set @uxsite)]
  ^-  (unit [from=@uxsite pro=sock-anno gen=state])
  =/  meme  (~(get ja memo.results.gen) fol)
  |-  ^-  (unit [@uxsite sock-anno state])
  ?~  meme  ~
  =*  i  i.meme
  ?.  (~(huge so less-memo.i) sock.sub)  $(meme t.meme)
  ::  memo hit: propagate subject needs
  :: 
  =/  sub-urge
    (urge:source (mask:source src.sub cape.sock.sub `stack) cape.less-code.i)
  ::
  =.  want.gen  (uni-urge:source want.gen sub-urge)
  =.  every.results.gen
    (~(put by every.results.gen) site less-code.i nomm.i)
  ::
  `[site.i prod.i gen]
::
++  melo
  |=  $:  site=@uxsite
          fol=*
          sub=sock-anno
          gen=state
          stack=(set @uxsite)
      ==
  ^-  (unit [from=@uxsite pro=sock-anno gen=state])
  =*  res  ,(unit [out=[@uxsite sock-anno gen=state] popped=(list cycle)])
  =/  =res
    =|  popped=(list cycle)
    |-  ^-  res
    =*  cycles-loop  $
    ?~  cycles.gen  ~
    =/  mele  (~(get ja melo.i.cycles.gen) fol)
    |-  ^-  res
    =*  mele-loop  $
    ?~  mele  cycles-loop(cycles.gen t.cycles.gen, popped [i.cycles.gen popped])
    =*  i  i.mele
    =/  want-site=cape  (~(gut by want.gen) site.i |)
    =/  mask=cape  (~(uni ca want-site) capture.i)
    =/  less  (~(app ca mask) sub.i)
    ?.  (~(huge so less) sock.sub)  mele-loop(mele t.mele)
    ::  melo hit: propagate subject needs
    :: 
    =/  sub-urge
      (urge:source (mask:source src.sub cape.sock.sub `stack) want-site)
    ::
    =.  want.gen  (uni-urge:source want.gen sub-urge)
    `[[site.i prod.i gen] popped]
  ::
  ::
  ?~  res  ~
  ::  top melo hit: no merging necessary
  ::
  ?:  =(~ popped.u.res)  `out.u.res
  =/  gen  gen.out.u.res
  ::  top cycle with a melo hit also needs to be merged
  ::
  =/  popped  (flop [i.-.cycles.gen popped.u.res])
  =.  cycles.gen  t.+.cycles.gen
  ::  merge all cycles up to & including melo-hit cycle top to bottom
  ::
  ?~  popped  !!
  =/  new-cycle  i.popped
  =/  rest  t.popped
  =.  new-cycle
    |-  ^-  cycle
    ?~  rest  new-cycle
    =.  entry.new-cycle  (min entry.new-cycle entry.i.rest)
    =.  frond.new-cycle  [%deep frond.new-cycle frond.i.rest]
    =.  set.new-cycle    [%deep set.new-cycle set.i.rest]
    =.  melo.new-cycle   ((~(uno by melo.new-cycle) melo.i.rest) weld-meal)
    ::
    $(rest t.rest)
  ::
  =.  cycles.gen  [new-cycle cycles.gen]
  `out.u.res(gen gen)
::  given kid and parent subject socks and parent evalsite label, check if
::  the kid sock is compatible with parent for a loop call. heuristic.
::  returns code usage cape if compatible
::
++  close
  |=  [kid-sub=sock par-sub=sock par-site=@uxsite gen=state]
  ^-  (unit cape)
  =/  par-want=cape  (~(gut by want.gen) par-site |)
  =/  par-masked=sock  (~(app ca par-want) par-sub)
  ?.  (~(huge so par-masked) kid-sub)  ~
  `par-want
::  fold flags of children expressions
::
++  fold-flag
  |=  l=(lest flags)
  ^-  flags
  =/  out=flags  i.l
  %+  roll  t.l
  |:  [f=*flags out=out]
  [|(loopy.f loopy.out) &(direct.f direct.out)]
::
++  jet-simple-gate-hoot
  =/  l=(list)
    =>  hoot
    :~  dec  add  sub  mul  div  mod  dvr  gte  gth  lte  lth  max  min
        cap  mas  peg  bex  can  cat  cut  end  fil  hew  lsh  met  rap
        rep  rev  rig  rip  rsh  run  rut  sew  swp  xeb
    ==
  |=  [s=* f=*]
  ^-  (unit (unit))
  ?~  l  ~
  ?:  &(=(f -.i.l) =(-.s -.i.l) =(+>.s +>.i.l))
    `(mure |.((slum i.l +<.s)))
  $(l t.l)
::
++  jet-simple-gate-play
  =/  l=(list)
    =>  playpen
    :~  dec  add  sub  mul  div  mod  dvr  gte  gth  lte  lth
        bex  can  cat  cut  end  fil  lsh  met  rap
        rep  rev  rip  rsh  swp  xeb
    ==
  |=  [s=* f=*]
  ^-  (unit (unit))
  ?~  l  ~
  ?:  &(=(f -.i.l) =(-.s -.i.l) =(+>.s +>.i.l))
    `(mure |.((slum i.l +<.s)))
  $(l t.l)
::
++  jet
  |=  [s=* f=*]
  ^-  (unit (unit))
  :: ~
  ?^  res=(jet-simple-gate-hoot s f)  ~&  %hit  res
  ?^  res=(jet-simple-gate-play s f)  res
  ::  place for jets with nontrivial templates
  ::
  ~
::  Analyze s/f pair, then run Nomm interpreter on the result
::  Indirect calls reanalyze
::  Direct calls are verified with subject sock nest checking
::
++  run-nomm
  |=  [s=* f=*]
  ^-  (unit)
  !.
  =/  gen
    :: ~>  %bout
    (scan s f)
  =/  n  nomm:(~(got by every.results.gen) 0x0)
  |-  ^-  (unit)
  ?-    n
      [p=^ q=*]
    =/  l  $(n p.n)
    ?~  l  ~
    =/  r  $(n q.n)
    ?~  r  ~
    `[u.l u.r]
  ::
      [%0 p=@]
    ?:  =(0 p.n)  ~&  '[%0 0]'  ~
    ?:  =(1 p.n)  `s
    =-  ~?  ?=(~ -)  '%0 crash'  -
    (mole |.(.*(s [0 p.n])))
  ::
      [%1 p=*]
    `p.n
  ::
      [%2 *]
    =/  s1  $(n p.n)
    ?~  s1  ~
    =/  f1  $(n q.n)
    ?~  f1  ~
    ?~  call=(~(get by every.results.gen) site.n)
      ~&  indirect+site.n
      (run-nomm u.s1 u.f1)
    ?.  (~(huge so less.u.call) & u.s1)
      ~|  site.n
      :: ~|  [need+less.u.call got+[& u.s1]]
      ~|  %sock-nest-error
      !!
    ?^  res=(jet u.s1 u.f1)  u.res
    $(s u.s1, n nomm.u.call)
  ::
      [%3 *]
    =/  p  $(n p.n)
    ?~  p  ~
    `.?(u.p)
  ::
      [%4 *]
    =/  p  $(n p.n)
    ?~  p  ~
    ?^  u.p  ~&  '%4 cell'  ~
    `+(u.p)
  ::
      [%5 *]
    =/  p  $(n p.n)
    ?~  p  ~
    =/  q  $(n q.n)
    ?~  q  ~
    `=(u.p u.q)
  ::
      [%6 *]
    =/  p  $(n p.n)
    ?~  p  ~
    ?+  u.p  ~&('%6 non-loobean' ~)
      %&  $(n q.n)
      %|  $(n r.n)
    ==
  ::
      [%7 *]
    =/  p  $(n p.n)
    ?~  p  ~
    $(s u.p, n q.n)
  ::
      [%10 *]
    ?:  =(0 p.p.n)  ~&  '%10 0'  ~
    =/  don  $(n q.p.n)
    ?~  don  ~
    =/  rec  $(n q.n)
    ?~  rec  ~
    =-  ~?  ?=(~ -)  '%10 crash'  -
    (mole |.(.*([u.don u.rec] [%10 [p.p.n %0 2] %0 3])))
  ::
      [%s11 *]
    $(n q.n)
  ::
      [%d11 *]
    =/  h  $(n q.p.n)
    ?~  h  ~
    $(n q.n)
  ::
      [%12 *]
    ~|  %no-scry  !!
  ==
--