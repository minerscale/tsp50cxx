%---------------------------------------------------------%
%                                                         %
%   TSP50C1x LPC SYNTHESIS PROGRAM                        %
%                                                         %
%   This is a sample speech synthesis program             %
%   which runs on the TSP50C1x family of speech           %
%   synthesis microprocessors.  It simply speaks the      %
%   numbers from one to five.                             %
%                                                         %
%   This program uses the D6 Coding table format.         %
%                                                         %
%---------------------------------------------------------%
%   COPYRIGHT 1989, 1992 TI - SPEECH PRODUCTS             %
%---------------------------------------------------------%
%   RAM MAP                                               %
%---------------------------------------------------------%
%   +----+----+----+----+----+----+----+----+
%   | 00 | 01 | 02 | 03 | 04 | 05 | 06 | 07 |
%   +----+----+----+----+----+----+----+----+
%   |    | EN | K12| K11| K10| K9 | K8 | K7 |
%   |    |    |    |    |    |    |    |    |
%   +----+----+----+----+----+----+----+----+
%   | 08 | 09 | 0A | 0B | 0C | 0D | 0E | 0F |
%   +----+----+----+----+----+----+----+----+
%   | K6 | K5 | K4 | K3 | K2 | K1 | C1 | C2 |
%   |    |    |    |    |    |    |    |    |
%   +----+----+----+----+----+----+----+----+
%   | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |
%   +----+----+----+----+----+----+----+----+
%   | EN | EN | PH      | PH      | K1      |
%   | V2 | V1 | V2      | V1      | V2      |
%   +----+----+----+----+----+----+----+----+
%   | 18 | 19 | 1A | 1B | 1C | 1D | 1E | 1F |
%   +----+----+----+----+----+----+----+----+
%   | K1      | K2      | K2      | K3      |
%   | V1      | V2      | V1      | V2      |
%   +----+----+----+----+----+----+----+----+
%   | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 |
%   +----+----+----+----+----+----+----+----+
%   | K3      | K4      | K4      | K5 | K5 |
%   | V1      | V2      | V1      | V2 | V1 |
%   +----+----+----+----+----+----+----+----+
%   | 28 | 29 | 2A | 2B | 2C | 2D | 2E | 2F |
%   +----+----+----+----+----+----+----+----+
%   | K6 | K6 | K7 | K7 | K8 | K8 | K9 | K9 |
%   | V2 | V1 | V2 | V1 | V2 | V1 | V2 | V1 |
%   +----+----+----+----+----+----+----+----+
%   | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 |
%   +----+----+----+----+----+----+----+----+
%   | K10| K10| K11| K11| K12| K12|TIMR|SCAL|
%   | V2 | V1 | V2 | V1 | V2 | V1 |    |    |
%   +----+----+----+----+----+----+----+----+
%   | 38 | 39 | 3A | 3B | 3C | 3D | 3E | 3F |
%   +----+----+----+----+----+----+----+----+
%   |FLAG|FLAG|MODE|ADR |ADR |    |    |    |
%   |    | 1  |BUF |MSB |LSB |    |    |    |
%   +----+----+----+----+----+----+----+----+
%   | 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 |
%   +----+----+----+----+----+----+----+----+
%   |    |    |    |    |    |    |    |    |
%   |    |    |    |    |    |    |    |    |
%   +----+----+----+----+----+----+----+----+
%   | 48 | 49 | 4A | 4B | 4C | 4D | 4E | 4F |
%   +----+----+----+----+----+----+----+----+
%   |    |    |    |    |    |    |    |    |
%   |    |    |    |    |    |    |    |    |
%   +----+----+----+----+----+----+----+----+
%   | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57 |
%   +----+----+----+----+----+----+----+----+
%   |    |    |    |    |    |    |    |    |
%   |    |    |    |    |    |    |    |    |
%   +----+----+----+----+----+----+----+----+
%   | 58 | 59 | 5A | 5B | 5C | 5D | 5E | 5F |
%   +----+----+----+----+----+----+----+----+
%   |    |    |    |    |    |    |    |    |
%   |    |    |    |    |    |    |    |    |
%   +----+----+----+----+----+----+----+----+
%   | 60 | 61 | 62 | 63 | 64 | 65 | 66 | 67 |
%   +----+----+----+----+----+----+----+----+
%   |    |    |    |    |    |    |    |    |
%   |    |    |    |    |    |    |    |    |
%   +----+----+----+----+----+----+----+----+
%   | 68 | 69 | 6A | 6B | 6C | 6D | 6E | 6F |
%   +----+----+----+----+----+----+----+----+
%   |    |    |    |    |    |    |    |    |
%   |    |    |    |    |    |    |    |    |
%   +----+----+----+----+----+----+----+----+
%   | 70 | 71 | 72 | 73 | 74 | 75 | 76 | 77 |
%   +----+----+----+----+----+----+----+----+
%   |    |    |    |    |    |    |    |    |
%   |    |    |    |    |    |    |    |    |
%   +----+----+----+----+----+----+----+----+
%   | 78 | 79 | 7A | 7B | 7C | 7D | 7E | 7F |
%   +----+----+----+----+----+----+----+----+
%   |    |    |    |    |    |    |    |    |
%   |    |    |    |    |    |    |    |    |
%   +----+----+----+----+----+----+----+----+
%
%---------------------------------------------------------%
%   ADDRESS LABELS FOR SYNTHESIS ROUTINE                  %
%---------------------------------------------------------%
%------------------------------------------------
%   SYNTHESISER RAM LOCATIONS
%------------------------------------------------
%   NOTE - NEVER CHANGE LOCATIONS #01 TO #0F
%
EN:         EQU #01 % Energy working value
K12:        EQU #02 % K12 working value
K11:        EQU #03 % K11 working value
K10:        EQU #04 % K10 working value
K9:         EQU #05 % K9 working value
K8:         EQU #06 % K8 working value
K7:         EQU #07 % K7 working value
K6:         EQU #08 % K6 working value
K5:         EQU #09 % K5 working value
K4:         EQU #0a % K4 working value
K3:         EQU #0b % K3 working value
K2:         EQU #0c % K2 working value
K1:         EQU #0d % K1 working value
C1:         EQU #0e % C1 paramater
C2:         EQU #0f % C2 parameter
ENV2:       EQU #10 % Energy new value MSB
ENV1:       EQU #11 % Energy current value MSB
PHV2:       EQU #12 % Pitch new Value MSB
PHV1:       EQU #14 % Pitch current value MSB
K1V2:       EQU #16 % K1 new value MSB
K1V1:       EQU #18 % K1 current value MSB
K2V2:       EQU #1a % K2 new value MSB
K2V1:       EQU #1c % K2 current value MSB
K3V2:       EQU #1e % K3 new value MSB
K3V1:       EQU #20 % K3 current value MSB
K4V2:       EQU #22 % K4 new value MSB
K4V1:       EQU #24 % K4 current value MSB
K5V2:       EQU #26 % K5 new value
K5V1:       EQU #27 % K5 current value
K6V2:       EQU #28 % K6 new value
K6V1:       EQU #29 % K6 current value
K7V2:       EQU #2a % K7 new value
K7V1:       EQU #2b % K7 current value
K8V2:       EQU #2c % K8 new value
K8V1:       EQU #2d % K8 current value
K9V2:       EQU #2e % K9 new value
K9V1:       EQU #2f % K9 current value
K10V2:      EQU #30 % K10 new value
K10V1:      EQU #31 % K10 current value
K11V2:      EQU #32 % K11 new value
K11V1:      EQU #33 % K11 current value
K12V2:      EQU #34 % K12 new value
K12V1:      EQU #35 % K12 current value
%
%
%   LPC status variable locations
%
TIMER:      EQU #36 % Stored timer value for update
SCALE:      EQU #37 % Interpolation factor INTP
FLAGS:      EQU #38 % Flags used in LPC synthesis
FLAG1:      EQU #39 % Flags used in LPC synthesis
MODE_BUF:   EQU #3a % Stored value of Mode register
ADR_MSB:    EQU #3b % MSB of address
ADR_LSB:    EQU #3c % LSB of address
%---------------------------------------------------------%
%   Constant Definitions                                  %
%---------------------------------------------------------%
%
%   Bit Size of Speech parameters
%
EBITS:      EQU 4   % Number of Energy Bits
PBITS:      EQU 7   % Number of Pitch Bits
RBITS:      EQU 1   % Number of Repeat Bits
K1BITS:     EQU 6   % Number of K1 bits
K2BITS:     EQU 6   % Number of K2 bits
K3BITS:     EQU 5   % Number of K3 bits
K4BITS:     EQU 5   % Number of K4 bits
K5BITS:     EQU 4   % Number of K5 bits
K6BITS:     EQU 4   % Number of K6 bits
K7BITS:     EQU 4   % Number of K7 bits
K8BITS:     EQU 3   % Number of K8 bits
K9BITS:     EQU 3   % Number of K9 bits
K10BITS:    EQU 3   % Number of K10 bits
K11BITS:    EQU 0   % Number of K11 bits
K12BITS:    EQU 0   % Number of K12 bits
%
%   Prescale Values
%
%   PSvalue = TRUNC(Samples * 2 * 30/256)
%
%   This comes from the fact that samples come ever 30
%   instruction cycles in LPC mode. The factor of 2
%   accounts for the cycle steal that happens in
%   LPC mode. When not in LPC mode, samples come
%   every 60 instruction cycles, so it comes out the
%   same.  The 256 divider is the full scale Timer
%   register value.
%
%
SAMPLES:    EQU 200              % Samples per frame
PSVALUE:    EQU (SAMPLES*60/256) % Prescale Value
%
%   Device Constants
%
C1_Value:   EQU #F61             % C1 Value
C2_Value:   EQU #F61             % C2 Value
MAX_RAM:    EQU #7F              % Highest RAM location
%
%   Speceal Energy Values
%
ESTOP:      EQU 15               % Stop code
ESILENCE:   EQU 0                % Silence code
%
%   Speceal Pitch Values
%
PUnVoiced:  EQU 0                % UnVoiced Frame Code
%
%
%   End of sentence signal
%
StopWord:   EQU #FF
%
%   FLAGS bit usage (and Set Masks)
%
STOPFLAG:   EQU #01              % Stop frame reached = 1
R_FLAG:     EQU #02              % Repeat Frame = 1
Update_Flg: EQU #04              % Set high on update
Sil_Flg1:   EQU #08              % New frame is silent = 1
Unv_Flg1:   EQU #10              % New frame is unvoiced = 1
Int_Inh:    EQU #20              % Inhibit interpolation = 1
Sil_Flg2:   EQU #40              % Current frame silent = 1
Unv_Flg2:   EQU #80              % Current frame unvoiced = 1
%
%   FLAG1 bit usage (and Set Masks)
%
Int_Off:    EQU #01              % Disable INTP routine = 1
%
%   MODE Register Bit Defintions
%
INT1:       EQU #01              % Enable Level 1 interrupt
LPC:        EQU #02              % Enable LPC synthesis
PCM:        EQU #04              % Enable PCM synthesis
INT2:       EQU #08              % Enable Level 2 interrupt
EXTROM:     EQU #10              % Set external ROM mode
RAMROM:     EQU #20              % Enable GETs from RAM
MASTER:     EQU #40              % Master/Slave Toggle
UNV:        EQU #80              % Enable Unvoiced excitation
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

            br      go          % yes, skip vector tables
            br      ram_loop    % no, go back
%
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

int1_01:    br      intp    % PPC < 200 hex interrupt

int2_00:
int2_01:
int2_10:
int2_11:
int1_00:
int1_10:
int1_11:    cla
            reti
%---------------------------------------------------------%
%   Speak phrases                                         %
%---------------------------------------------------------%
go:         tca     0       % Speak 1st phrase
            call    speak

            tca     1       % Speak 2nd phrase
            call    speak

            tca     2       % Speak 3rd phrase
            call    speak

            setoff          % Quit program
%---------------------------------------------------------%
%   Speak Utterance - Phrase number in A register         %
%---------------------------------------------------------%
speak:      intgr
            sala            % Double index to get offset
            acaac sentence  % Add base of table
            luab            % Get address MSB
            iac
            luaa            % Get address LSB
            xba
            sala4           % Combine MSB and LSB
            sala4
            abaac

            tab             % save address
            tamd  ADR_LSB   % save lsb of address

            axca  1         % shift address right by 8 bits
            sara

            tamd  ADR_MSB   % save MSB of address
            xba
            br    speak2

speak1:     tmad  ADR_LSB   % fetch and combine address
            tab
            tmad  ADR_MSB
            sala4
            sala4
            abaac

            iac             % increment address

            tab             % save new address
            tamd  ADR_LSB   % save LSB of address

            axca 1          % shift address right by 8 bits
            sara

            tamd  ADR_MSB   % save MSB of address
            xba

speak2:     luaa            % get word number
            anec  StopWord  % end of phrase?
            br    speak3    % no, continue
            retn            % yes, exit loop

speak3:     sala            % double index to get offset
            acaac speech    % add base of table
            luab            % get address MSB
            iac
            luaa            % get address LSB
            xba
            sala4           % combine LSB and MSB
            sala4
            abaac

            luaps           % load speech address register

            cla             % kill K11 and K12 parameters
            tamd   K11
            tamd   K12

            tamd   FLAGS    % Init flags for speech

            cla             % load C2 parameter (a device constant)
            acaac  C2_Value
            tamd   C2

            cla             % load C1 paramater (a device constant)
            acaac  C1_Value
            tamd   C1
%
% Now we give an initial value to the Pitch in case the
% utterance starts witha silent frame.
%
            acaac  #0c
            tamd   PHV1
            tamd   PHV2
%
% Now we preload the first two frames.
%
            call   update   % load first frame
            call   update   % load second frame
%
% Now we give some values to the Timer and Prescaler so
% that we can do a valid interpolation on the first call to
% INTP.  Then we do the first call to INTP to preload the
% first valid interpolation.
%
            tca    PSVALUE  % initialise prescale
            tapsc
            tca    #7f      % pretend there was a previous update
            tamd   TIMER
            tca    #ff      % set timer to max value to disable interpolation
            tatm
            call   intp     % do first interpolation

%
% Now we enable the synthesiser for speech
%
% We do this in two stages so that we can reset the
% interrupt pending latch without it being immediately
% set again by the B1(low) interrupt.
%
            tcx    MODE_BUF % turn on LPC synthesiser
            orcm   LPC
            tma
            tamode

            reti            % Reset interrupt pending latch

            orcm   INT1     % Enable interrupt
            tma
            tamode

%
% Now we loop until the utterance is complete. When the
% utterance is finished. the routine UPDATE will execute a
% RETN instruction which will exit this routine. In the
% meantime, this loop will poll the Timer register and
% update the frame whenever it underflows.
%
speak_lp:
            tcx     FLAGS
            tstcm   Update_Flg % is update already done?
            br      speak_lp   % yes, loop

            tcx     TIMER      % get old timer register value into B register
            tma
            tab

            ttma               % get new timer register value and scale it
            sara

            tam                % store new value
            xba                % exchange new and old values
            sbaan              % subtract new from old
            br      update     % if underflowed, do an update

            tma                % get new timer value again.
            anec    0          % Is it about to underflow?
            br      speak_lp   % no, loop again
            br      update     % yes, do update now
% % % % %
% INTERPOLATION ROUTINE
% % % % %
% First we need to get the current value of the timer
% register and store it away.  It will be divided by two
% with the SARA instruction so that the most significant
% bit is garanteed to be zero so that it will always be
% interpreted as a positive number during the
% interpolation.
% % % % %
intp:       intgr              % ensure that we are in integer mode
            ttma               % get timer register contents
            sara               %   shift to make positive
            tamd    SCALE      %   and store it
% % % %
% See if this routine is enabled.  If it is not, exit
% the routine.
% % % %
            tcx     FLAG1      % point to flag
            tstcm   Int_Off    % if routine disabled...
            br      ireti      % ...branch to exit point
% % % % %
% Next we need to see if the frame type has changed between
% voiced and unvoiced frames.  If it has, we do not want to
% interpolate between frames; we just want to use the current
% frame values until we have two frames of the same type to
% interpolate between.
% % % % %
tintp:      tcx     FLAGS      % point to status flags
            tstcm   Int_Inh    % Is interpolation inhibited?
            br      noint      % yes, inhibit interpolation
            br      intpch     % no, interpolate
% % % % %
% The following code is reached if interpolation is
% inhibited. It sets the stored timer value to #7F which
% effectively forces the interpolation to yield the old
% values for the working values, thus effectively disabling
% interpolation.
% % % % %
noint:      tca     #7f        % set scaled factor to highest value
            tamd    SCALE
%
% If the new frame has a voicing different from the last
% frame, we want to zero the energy until the Unvoiced bit
% in the mode register is changed and the K parameters are
% all to the correct values. We therefore check in this
% section of code to see if the frame voicing is different
% from the setting in the Mode Register. If it is, we zero
% the energy until after the Mode Register is modified.
%
            tcx     FLAGS
            tstcm   Unv_Flg2   % is current frame unvoiced?
            br      uv         % yes, go to unvoiced branch

            tcx     MODE_BUF   % current frame is voiced
            tstcm   unv        % has mode changed to unvoiced?
            br      ClrEN      % yes, clear the energy
            br      intpch     % no, no action required

Uv:         tcx     MODE_BUF   % new frame is unvoiced
            tstcm   unv        % has voicing mode changed?
            br      intpch     % no, no action required

ClrEN:      cla                % zero energy during update
            tamd    EN
            br      intpch

%
% Interpolate Pitch and write the result to the pitch
% register
%
intpch:     tcx     PHV2       % combine new pitch and new
            tmaix              %   fractional pitch and
            sala4              %   leave in the B register
            amaac
            ixc
            tab
            tmaix              % combine current pitch and
            sala4              %   current fractional pitch
            amaac              %   and leave in A register

            sbaan              % (Pcurrent - Pnew)
            tcx     SCALE
            axma               % (Pcurrent-Pnew)*Timer
            abaac              % Pnew + (Pcurrent - Pnew)*Timer
            sala               % Adjust for 2 byte excitation
            tasyn              % write to pitch register
%
% Interpolate K1 and store the result in the working K1
% register
%
            extsg              % allow negative K parameters
            tcx     K1V2       % combine new k1 and new
            tmaix              %   fractional K1 and
            sala4              %   leave in the B register
            amaac
            ixc
            tab

            tmaix              % combine current K1 and
            sala4              %   current fractional K1 and
            amaac              %   leave in the A register

            sbaan              % (K1current - K1new)
            tcx     SCALE
            axma               % (K1current - K1new)*Timer
            abaac              % K1new + (K1current - K1new)*Timer
            tmad    K1         % load interpolated K1 value
%
% Interpolate K2 and store the result in the
% working K2 register
%

%---------------------------------------------------------%
%   This is the lookup table given the starting address   %
%   of each concatenation list.                           %
%---------------------------------------------------------%
sentence:   DATA    phrase0
            DATA    phrase1
            DATA    phrase2

%---------------------------------------------------------%
%   This is the concatenation table giving the lists      %
%   of word numbers that define each phrase. Each         %
%   list is terminated by an #FF                          %
%---------------------------------------------------------%
phrase0:    BYTE    1,2,3,4,#FF
phrase1:    BYTE    4,3,2,1,#FF
phrase2:    BYTE    5,4,3,2,1,#FF

%---------------------------------------------------------%
%   This is the concatenation table giving the lists      %
%   of word numbers that define each phrase. Each         %
%   list is terminated by an #FF                          %
%---------------------------------------------------------%
speech:     DATA    #0000
            DATA    #0000+VOC % Word 1 "One"
            DATA    #0084+VOC % Word 2 "Two"
            DATA    #00F6+VOC % Word 3 "Three"
            DATA    #017A+VOC % Word 4 "Four"
            DATA    #01E0+VOC % Word 5 "Five"
            DATA    #028C+VOC % Word 6 "Six"
