%---------------------------------------------------------%
%   Start of program                                      %
%---------------------------------------------------------%
            AORG    #0000
            tmad    0

%----------Initialise mode register-----------------------%
            cla
            tamode

%----------Clear all ram to zero--------------------------%
            clx                 % Start at bottom of RAM
ram_loop:   tamix               % Clear RAM, increment pointer
            xgec    MAX_RAM + 1 % Finished all RAM?

            br      GO          % yes, skip vector tables
            br      RAM_LOOP    % no, go back

%---------------------------------------------------------%
%   Interrupt vectors                                     %
%---------------------------------------------------------%
            AORG    #0010
            sbr     int2_01 % Timer Underflow, PCM=0, LPC=1
            sbr     int2_01 % Timer Underflow, PCM=0, LPC=1
            sbr     int2_00 % Timer Underflow, PCM=0, LPC=0
            sbr     int2_00 % Timer Underflow, PCM=0, LPC=0
            sbr     int2_11 % Timer Underflow, PCM=1, LPC=1
            sbr     int2_11 % Timer Underflow, PCM=1, LPC=1
            sbr     int2_10 % Timer Underflow, PCM=1, LPC=0
            sbr     int2_10 % Timer Underflow, PCM=1, LPC=0
            sbr     int1_01 % PPC < 200 hex interrupt
            sbr     int1_01 % PPC < 200 hex interrupt
            sbr     int1_00 % Pin (B1) goes low interrupt
            sbr     int1_00 % Pin (B1) goes low interrupt
            sbr     int1_11 % 10 kHz Clock interrupt
            sbr     int1_11 % 10 kHz Clock interrupt
            sbr     int1_10 % 20 kHz Clock interrupt
            sbr     int1_10 % 20 kHz Clock interrupt

int1_01:    br      INTP    % PPC < 200 hex interrupt
int2_00:
int2_01:
int2_10:
