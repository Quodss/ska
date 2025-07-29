/-  *noir
|%
::  no registerization for now
::
::  Simple stack-based VM that serves as a compilation target for Nomm.
::  Every program pops its subject from the stack and pushes the result
::
::  Global compilation state
::
+$  line
  $:  progs=(map glob-atom prog)
      fols=(jar * prog)
  ==
::  a program: body, requirements for entry (subject template, formula)
:: 
+$  prog
  $:  body=(list op)
      less=sock
      fol=*
  ==
::  stack VM ops
::  when compiling %2 to %call and %calf q.nomm should be ignored
::  (never crashes, know the result)
::
+$  op  ::  XX scrying, hints
  $~  %bail
  $@  $?  %slow  ::  [fol sub ...]      -->  [pro ...], nock 2 indirect call
          %swap  ::  [som mos ...]      -->  [mos som ...]
          %cons  ::  [tel hed ...]      -->  [pro ...]
          %depf  ::  [som ...]          -->  [lob ...], nock 3
          %rise  ::  [som ...]          -->  [som + 1 ...], nock 4
          %equi  ::  [som mos ...]      -->  [lob ...], nock 5
          %bail  ::  crash
          %copy  ::  [som ...]          -->  [som som ...]
          %lose  ::  [som ...]          -->  [...]
      ==
  $%  [%axis p=@]                 ::  [sub ...]      -->  [pro ...], nock 0
      [%call p=glob-atom]         ::  [sub ...]      -->  [pro ...], nock 2 direct call
      [%calf p=glob-atom q=bell]  ::  [sub ...]      -->  [pro ...], nock 2 direct call, jetted
      [%jump p=glob-atom]         ::  tail calls
      [%jumf p=glob-atom q=bell]  ::  
      [%cnst p=*]                 ::  [...]          -->  [p ...], nock 1
      [%skip p=@]                 ::  skip {p} instructions unconditionally
      [%skim p=@]                 ::  [lob ...]      -->  [...], skip {p} instructions if p == 0, else crash if p != 1 
      [%edit p=@]                 ::  [don rec ...]  -->  [pro ...], edit {rec} with {don} at {p}, nock 10
  ==
--