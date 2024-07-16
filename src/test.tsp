      cla           % clear the A register
      intgr         % put chip in integer mode
      acaac  #fe    % add #fe to A register
loop: iac           % increment A register
      BR     end    % status is only set on overflow
      BR     loop   % branch sets status, so this is unconditional
end:  setoff        % halt
      AORG   #10
      BYTE   #69
      BYTE   #42
      BYTE   #de
      BYTE   #ad
      BYTE   #be
      BYTE   #ef
