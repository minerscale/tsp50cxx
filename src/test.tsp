      cla           % clear the A register
      intgr         % put chip in integer mode
      acaac  #fe    % add #fe to A register
🍆:   iac           % increment A register
      BR     😏     % status is only set on overflow
      BR     🍆     % branch sets status, so this is unconditional
😏:   setoff        % halt
      AORG   #10
      BYTE   #69,#42,#de,#ad,#be,#ef
      AORG   #20
      DATA   #DEAD,#BEEF
      AORG   #30
      TEXT   "Hello, I am calling you from Microsoft"
