      CLA           % clear the A register
      INTGR         % put chip in integer mode
      ACAAC  #fe    % add #fe to A register
loop: IAC           % increment A register
      Br     end    % status is only set on overflow
      Br     loop   % branch sets status, so this is unconditional
end:  SETOFF        % halt
