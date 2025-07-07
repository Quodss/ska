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
::  error: either m or parent-kid pair which turned out to be false
::
++  error
  |$  [m]
  (each m (pair @uxsite @uxsite))
::
+$  err-state  (error state)
+$  frond  (deep [par=@uxsite kid=@uxsite par-sub=sock kid-sub=sock])
+$  cycle
  $:  entry=@uxsite
      latch=@uxsite
      =frond
      set=(set @uxsite)
      pars=(set @uxsite)
  ==
::
++  add-frond
  |=  [new=[par=@uxsite kid=@uxsite sock sock] cycles=(list cycle)]
  ^-  (list cycle)
  ?:  |(?=(~ cycles) (gth par.new latch.i.cycles))
    ::  push new cycle
    ::
    :_  cycles
    ^-  cycle
    [par.new kid.new [%list new ~] (silt par.new kid.new ~) [par.new ~ ~]]
  ::  pop and extend top cycle
  ::
  =/  new-cycle=cycle
    :*  (min par.new entry.i.cycles)
        kid.new
        (dive frond.i.cycles new)
        (~(gas in set.i.cycles) ~[kid.new par.new])
        (~(put in pars.i.cycles) par.new)
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
  =.  set.new-cycle    (~(uni in set.new-cycle) set.i.rest)
  =.  pars.new-cycle   (~(uni in pars.new-cycle) pars.i.rest)
  $(rest t.rest)
::
+$  state
  ::  global state
  ::    evals:    call info
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
  ::           done)  XX should probably be `deep`?
  ::      pars: set of parents in the cycle (to save code in the current cycle)
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
  $:  =evals
      =results
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
    fols=(jar * (pair sock @uxsite))
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
  =|  =blocklist
  |-  ^-  [[sock-anno flags] state]
  =*  redo-loop  $
  =;  res
    ?-  -.res
      %&  p.res
      %|  ~&  %redo  ~|  p.res  !!  ::  redo-loop(blocklist (~(put ju blocklist) p.res))
    ==
  ^-  (error [[sock-anno flags] state])
  ::  record current evalsite in the subject provenance tree
  ::
  =.  src.sub
    ?~  src.sub  [[one here-site]~ ~ ~]
    src.sub(n [[one here-site] n.src.sub])
  ::  register evalsite in bidirectional mapping
  ::
  =.  sites.evals.gen  (~(put by sites.evals.gen) here-site sock.sub fol)
  =.  calls.evals.gen  (~(add ja calls.evals.gen) fol here-site sock.sub)
  ::  check memo cache
  ::
  ?^  m=(memo here-site fol sub gen set.stack)
    =.  bars.gen
      %:  ps  bars.gen  'memo:'
        (rap 3 (scux here-site) ' <- ' (scux from.u.m) ~)
        --0
      ==
    ::
    &+[[pro.u.m deff] gen.u.m]
  ::  XX to do meloization
  ::
  ::  push on the stack
  ::
  =.  list.stack  [[sock.sub fol here-site] list.stack]
  =.  fols.stack  (~(add ja fols.stack) fol sock.sub here-site)
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
      =.  want.gen
        %-  (~(uno by want.gen) fol-urge)
        |=  [@uxsite a=cape b=cape]
        ~(cut ca (~(uni ca a) b))
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
        ?.  ?&  !(~(has ju blocklist) q.i.tak there-site)
                (close sock.s-prod p.i.tak q.i.tak gen)
            ==
          stack-loop(tak t.tak)
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
        ::
        =.  cycles.gen
          (add-frond [q.i.tak there-site p.i.tak sock.s-prod] cycles.gen)
        ::  register evalsite in bidirectional mapping
        ::  (it's a direct call but we don't analyze through so we have to
        ::  put registration code here)
        ::
        =.  sites.evals.gen
          (~(put by sites.evals.gen) there-site sock.s-prod fol-new)
        ::
        =.  calls.evals.gen
          (~(add ja calls.evals.gen) fol-new there-site sock.s-prod)
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
  =/  less-code=sock  ~(norm so (~(app ca want-site) sock.sub))
  ::  minified subject sock for memo: stricter requirement i.e. bigger sock,
  ::  includes possible subject captures
  ::
  =/  less-memo=(trap sock)
    |.
    ::  parts of subject that may have been captured by the result and thus
    ::  could be used as code by cousin evalsites
    ::
    =/  capture-res=cape
      (~(gut by (urge:source src.prod cape.sock.prod)) here-site |)
    ::
    =/  mask=cape  (~(uni ca want-site) capture-res)
    =/  less  ~(norm so (~(app ca mask) sock.sub))
    ::  we start off with more knowledge in the subject and mask down, 
    ::  so the intersection of want-site and cape.sock.sub should be exactly
    ::  equal to want-site?
    ::
    ?.  =(mask cape.less)
      ~_  'cape.less < mask'
      ~|  [cape.less mask]
      !!
    less
  ::  |.(sock)
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
    (final-simple here-site code less-memo prod gen direct.flags want-site)
  =*  i  ,.-.cycles.gen
  ?.  =(here-site entry.i)
    &+[& (process here-site code prod gen direct.flags)]
  ::  cycle entry not loopy if finalized
  ::
  =-  ?:  ?=(%| -<)  -  &+[| p]
  ^-  err-state
  %:  final-cycle
    here-site
    code
    less-code
    less-memo
    prod
    frond.i
    gen
    direct.flags
    want-site
  ==
::  finalize analysis of non-loopy formula
::
++  final-simple
  |=  $:  site=@uxsite
          code=nomm
          less-memo=(trap sock)
          prod=sock-anno
          gen=state
          direct=?
          want-site=cape
      ==
  ^-  state
  =.  bars.gen  (ps bars.gen 'done:' (scux site) -1)
  =/  mayb-site=(unit cape)  (~(get by want.gen) site)
  ::  memoize if fully direct
  ::
  =?  memo.results.gen  direct
    %-  ~(put by memo.results.gen)
    :-  site
    :^    code
        ::  minimized subject sock for memo checks
        ::
        $:less-memo
      ::  full result, captured subject was included in memo requirement
      ::
      prod
    ::  subject code usage for subject need propagation on memo hits
    ::
    want-site
  ::
  =?  want.gen  ?=(^ mayb-site)  (~(del by want.gen) site)
  gen
::  finalize analysis of a call graph cycle entry: pop cycle, verify assumptions
::
++  final-cycle
  |=  $:  site=@uxsite
          code=nomm
          less-code=sock
          less-memo=(trap sock)
          prod=sock-anno
          =frond
          gen=state
          direct=?
          want-site=cape
      ==
  ^-  err-state
  =^  pop=cycle  cycles.gen  ?~(cycles.gen !! cycles.gen)
  =/  err-gen=err-state
    %+  roll-deep  frond
    |:  :-  *[par=@uxsite kid=@uxsite par-sub=sock kid-sub=sock]
        err-gen=`err-state`&+gen
    ^-  err-state
    ::  XX performance: return sooner? OTOH roll is jetted and errors should be rare
    ::
    ?:  ?=(%| -.err-gen)  err-gen
    =/  par-want=cape  (~(gut by want.gen) par |)
    =/  par-masked=sock  (~(app ca par-want) par-sub)
    ?.  (~(huge so par-masked) kid-sub)  ::  |+[par kid]
      ~|  [par kid]
      ~|  par-want
      !!
    =.  every.results.p.err-gen
      %+  ~(put by every.results.p.err-gen)  kid
      ?:  =(par site)  [less-code code]
      (~(got by every.results.gen) par)
    ::
    err-gen
  ::
  ?:  ?=(%| -.err-gen)  err-gen
  =.  bars.p.err-gen  (ps bars.p.err-gen 'fini:' (scux site) -1)
  =.  want.p.err-gen
    %-  ~(rep in set.pop)
    |:  [v=*@uxsite acc=want.p.err-gen]
    (~(del by acc) v)
  ::  memoize if fully direct
  ::
  =?  memo.results.p.err-gen  direct
    %-  ~(put by memo.results.gen)
    :-  site
    :^    code
        $:less-memo
      prod
    want-site
  ::
  err-gen
::  treat analysis result of a non-finalized evalsite
::
++  process
  |=  [site=@uxsite code=nomm prod=sock-anno gen=state direct=?]
  ^-  state
  =.  bars.gen  (ps bars.gen 'ciao:' (scux site) -1)
  ::  TODO meloization
  ::
  ?~  cycles.gen  !!
  =.  set.i.cycles.gen   (~(put in set.i.cycles.gen) site)
  :: =/  has-in-pars=?  (~(has in pars.i.cycles.gen) site)
  :: =?  want.gen  has-in-pars  (~(put by want.gen) site cape.less)
  gen
::
++  memo
  |=  [site=@uxsite fol=* sub=sock-anno gen=state stack=(set @uxsite)]
  ^-  (unit [from=@uxsite pro=sock-anno gen=state])
  =/  calls  (~(get ja calls.evals.gen) fol)
  |-  ^-  (unit [@uxsite sock-anno state])
  ?~  calls  ~
  ?~  res=(~(get by memo.results.gen) site.i.calls)  $(calls t.calls)
  ?.  (~(huge so less.u.res) sock.sub)               $(calls t.calls)
  ::  memo hit: propagate subject needs
  :: 
  =/  sub-urge
    (urge:source (mask:source src.sub cape.sock.sub `stack) want.u.res)
  ::
  =.  want.gen
    %-  (~(uno by want.gen) sub-urge)
    |=  [@uxsite a=cape b=cape]
    ~(cut ca (~(uni ca a) b))
  ::
  =.  every.results.gen
    (~(put by every.results.gen) site less.u.res nomm.u.res)
  ::
  :-  ~
  :-  site.i.calls
  :_  gen
  prod.u.res
::  given kid and parent subject socks and parent evalsite label, check if
::  the kid sock is compatible with parent for a loop call. heuristic.
::
++  close
  |=  [kid-sub=sock par-sub=sock par-site=@uxsite gen=state]
  ^-  ?
  =/  par-want=cape  (~(gut by want.gen) par-site |)
  =/  par-masked=sock  (~(app ca par-want) par-sub)
  (~(huge so par-masked) kid-sub)
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
  ~
  :: ?^  res=(jet-simple-gate-hoot s f)  ~&  %hit  res
  :: ?^  res=(jet-simple-gate-play s f)  res
  :: ::  place for jets with nontrivial templates
  :: ::
  :: ~
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