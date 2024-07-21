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
PSVALUE:    EQU SAMPLES*60/256   % Prescale Value
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
            tstcm   UNV        % has mode changed to unvoiced?
            br      ClrEN      % yes, clear the energy
            br      intpch     % no, no action required

uv:         tcx     MODE_BUF   % new frame is unvoiced
            tstcm   UNV        % has voicing mode changed?
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
            tcx     K2V2       % combine new K2 and new fractional
            tmaix              % K2 and leave in the B register
            sala4
            amaac
            ixc
            tab

            tmaix              % combine current K2 and
            sala4              %   current fractinoal K2 and
            amaac              %   leave in the A register

            sbaan              % (K2current - K2new)
            tcx     SCALE
            axma               % (K2current - K2new)*Timer
            abaac              % K2new + (K2current - K2new)*Timer
            tamd    K2         % load interpolated K2 value
%
% Interpolate K3 and store the result in the
% working K3 register
%
            tcx     K3V2       % combine new K3 and new fractional
            tmaix              % K3 and leave in the B register
            sala4
            amaac
            ixc
            tab

            tmaix              % combine current K3 and
            sala4              %   current fractinoal K3 and
            amaac              %   leave in the A register

            sbaan              % (K3current - K3new)
            tcx     SCALE
            axma               % (K3current - K3new)*Timer
            abaac              % K3new + (K3current - K3new)*Timer
            tamd    K3         % load interpolated K3 value
%
% Interpolate K4 and store the result in the
% working K4 register
%
            tcx     K4V2       % combine new K4 and new fractional
            tmaix              % K4 and leave in the B register
            sala4
            amaac
            ixc
            tab

            tmaix              % combine current K4 and
            sala4              %   current fractinoal K4 and
            amaac              %   leave in the A register

            sbaan              % (K4current - K4new)
            tcx     SCALE
            axma               % (K4current - K4new)*Timer
            abaac              % K4new + (K4current - K4new)*Timer
            tamd    K4         % load interpolated K4 value
%
% Interpolate K5 and store the result in the
% working K5 register
%
            tcx     K5V2       % put new K5 (adjusted to 12 bits)
            tmaix              %   in B register
            sala4
            tab
            tmaix              % put current K5 (adjusted to 12 bits)
            sala4              %   in A register
            
            sbaan              % (K5current - K5new)
            tcx     SCALE
            axma               % (K5current - K5new)*Timer
            abaac              % K5new + (K5current - K5new)*Timer
            tamd    K5         % load interpolated K5 value
%
% Interpolate K6 and store the result in the
% working K6 register
%
            tcx     K6V2       % put new K6 (adjusted to 12 bits)
            tmaix              %   in B register
            sala4
            tab
            tmaix              % put current K6 (adjusted to 12 bits)
            sala4              %   in A register
            
            sbaan              % (K6current - K6new)
            tcx     SCALE
            axma               % (K6current - K6new)*Timer
            abaac              % K6new + (K6current - K6new)*Timer
            tamd    K6         % load interpolated K6 value
%
% Interpolate K7 and store the result in the
% working K7 register
%
            tcx     K7V2       % put new K7 (adjusted to 12 bits)
            tmaix              %   in B register
            sala4
            tab
            tmaix              % put current K7 (adjusted to 12 bits)
            sala4              %   in A register
            
            sbaan              % (K7current - K7new)
            tcx     SCALE
            axma               % (K7current - K7new)*Timer
            abaac              % K7new + (K7current - K7new)*Timer
            tamd    K7         % load interpolated K7 value
%
% Interpolate K8 and store the result in the
% working K8 register
%
            tcx     K8V2       % put new K8 (adjusted to 12 bits)
            tmaix              %   in B register
            sala4
            tab

            tmaix              % put current K8 (adjusted to 12 bits)
            sala4              %   in A register
            
            sbaan              % (K8current - K8new)
            tcx     SCALE
            axma               % (K8current - K8new)*Timer
            abaac              % K8new + (K8current - K8new)*Timer
            tamd    K8         % load interpolated K8 value
%
% Interpolate K9 and store the result in the
% working K9 register
%
            tcx     K9V2       % put new K9 (adjusted to 12 bits)
            tmaix              %   in B register
            sala4
            tab

            tmaix              % put current K9 (adjusted to 12 bits)
            sala4              %   in A register

            sbaan              % (K9Current - K9New)
            tcx     SCALE
            axma               % (K9current - K9new)*Timer
            abaac              % K9new + (K9current - K9new)*Timer
            tamd    K9         % load interpolated K9 value
%
% Interpolate K10 and store the result in the
% working K10 register
%
            tcx     K10V2      % put new K10 (adjusted to 12 bits)
            tmaix              %   in B register
            sala4
            tab

            tmaix              % put current K10 (adjusted to 12 bits)
            sala4              %   in A register

            sbaan              % (K10Current - K10New)
            tcx     SCALE
            axma               % (K10current - K10new)*Timer
            abaac              % K10new + (K10current - K10new)*Timer
            tamd    K10        % load interpolated K10 value

%
% K11 and K12 are not needed for LPC 10, so they have been
% commented out.
%
% Interpolate K11 and store the result in the
% working K11 register
%
%           tcx     K11V2      % put new K11 (adjusted to 12 bits)
%           tmaix              %   in B register
%           sala4
%           tab

%           tmaix              % put current K11 (adjusted to 12 bits)
%           sala4              %   in A register

%           sbaan              % (K11Current - K11New)
%           tcx     SCALE
%           axma               % (K11current - K11new)*Timer
%           abaac              % K11new + (K11current - K11new)*Timer
%           tamd    K11        % load interpolated K11 value
%
% Interpolate K12 and store the result in the
% working K12 register
%
%           tcx     K12V2      % put new K12 (adjusted to 12 bits)
%           tmaix              %   in B register
%           sala4
%           tab

%           tmaix              % put current K12 (adjusted to 12 bits)
%           sala4              %   in A register

%           sbaan              % (K12Current - K12New)
%           tcx     SCALE
%           axma               % (K12current - K12new)*Timer
%           abaac              % K12new + (K12current - K12new)*Timer
%           tamd    K12        % load interpolated K12 value
%
%
% Interpolate Energy
%
%
            intgr              % back to integer mode for energy
            tcx     ENV2       % combine new energy and fractional
            tmaix              % energy and leave in the B register
            sala4
            tab
            tmaix              % combine current energy and
            sala4              %    current fractional energy
            sbaan              % (Ecurrent - Enew)
            tcx     SCALE
            axma               % (Ecurrent - Enew) * Timer
            abaac              % Enew + (Ecurrent - Enew) * Timer
            xba                % save energy
%
% Set voiced/unvoiced mode according to current frame type.
% This is done in a two step fashion:  first the value in
% the MODE_BUF register is adjusted iwth an AND or OR
% operation, then the result is written to the synthesiser
% with a TAMODE operation.  We do it this way to keep a copy
% of the current status of the synthesiser mode at all times.
%
stmode:     tcx     FLAGS
            andcm  ~Update_Flg % signal that interp done
            tstcm   Unv_Flg2   % Is current frame unvoiced?
            br      setuv      % yes, set mode to unvoiced
            tcx     MODE_BUF   % no, ...
            andcm  ~UNV        % ...set mode to voiced
            br      writemode

setuv:      tcx     MODE_BUF   % current frame is unvoiced, so
            orcm    UNV        % set mode to unvoiced.

writemode:  tma                % write mode information
            tamode             % to mode register

            xba                % write mode information
            tamd    EN         % to filter

ireti:      reti               % return from interrupt
            retn               % return from first call
% Update the parameters for a new frame
%
% First we inhibit the operation of the interpolation
% routine.
%
update:     tcx     MODE_BUF
            andcm  ~INT1
            tma
            tamode
%
% To preven double updates, if the stored value of the
% timer register is zero, then we need to change it to #7F.
% If we do not do this, then the polling routine will discover
% an underflow and call Update a second time.
%
            tcx     TIMER      % get stored value
            tma                %   of Timer into A

            anec    0          % Is it zero?
            br      updt00     % no, do nothing
            tca     #7f        % yes, replace value
            tam
%
% First we need to test to see if a stop frame was
% encountered on the last pass through the routine.  If the
% previous frame was a stop frame, we need to turn off the
% synthesiser and stop speaking.
%
updt00:     tcx     FLAGS
            tstcm   STOPFLAG   % Was stop frame encountered?
            br      stop       %   yes, stop speaking
%
% Transfer the state of the previous frame to the Unvoiced
% flag (Current).
%
            tstcm   Unv_Flg1   % Was previous frame unvioced?
            br      sunvl      %   yes, current frame = unvoiced
            andcm  ~Unv_Flg2   %   no, current frame = voiced
            br      tsil       %   and continue

sunvl:      orcm    Unv_Flg2   % Set current frame unvoiced.
%
% Tranfer the state of the previous frame to the
% Silence flag (Current).
%
tsil:       tstcm   Sil_Flg1   % Was previous frame silent?
            br      ssil       %   yes, current frame silent
            andcm  ~Sil_Flg2   %   no, current frame not sil.
            br      zroflg     %   and continue

ssil:       orcm    Sil_Flg2   % Set current frame to silent
%
% Reset the Repeat Flag, new Silence Flag, new Unvoiced
% Flag, and Interpolation Inhibit flag so that new
% valnues can be loaded in this routine.
%
zroflg:     tcx     FLAGS
            andcm   #c5
%
% Transfer the new frame parameters into the
% storage location used for the current frame parameters.
%
            tcx     ENV2       % Transfer new frame energy 
            tmaix              %   from new frame location
            tamix              %   to current frame location
%-----PITCH-----
            tmaix              % Transfer new frame pitch
            tamd    PHV1       %   to current frame location

            tmaix              % Transfer new fration pitch
            ixc                %   to current frame location
            tamix
%-----K1------
            tmaix              % Transfer new frame K1 param.
            tamd    K1V1       %   to current frame location
            tmaix              % Transfer new fration K1
            ixc                %   to current frame location
            tamix
%-----K2------
            tmaix              % Transfer new frame K2 param.
            tamd    K2V1       %   to current frame location
            tmaix              % Transfer new fration K2
            ixc                %   to current frame location
            tamix
%-----K3------
            tmaix              % Transfer new frame K3 param.
            tamd    K3V1       %   to current frame location
            tmaix              % Transfer new fration K3
            ixc                %   to current frame location
            tamix
%-----K4------
            tmaix              % Transfer new frame K4 param.
            tamd    K4V1       %   to current frame location
            tmaix              % Transfer new fration K4
            ixc                %   to current frame location
            tamix
%-----K5------
            tmaix              % Transfer new frame K5 param.
            tamix              %   to current frame location
%-----K6------
            tmaix              % Transfer new frame K6 param.
            tamix              %   to current frame location
%-----K7------
            tmaix              % Transfer new frame K7 param.
            tamix              %   to current frame location
%-----K8------
            tmaix              % Transfer new frame K8 param.
            tamix              %   to current frame location
%-----K9------
            tmaix              % Transfer new frame K9 param.
            tamix              %   to current frame location
%-----K10------
            tmaix              % Transfer new frame K10 param.
            tamix              %   to current frame location
%
% K11 and K12 are not used in LPC 10 synthesis.  The code
% has been commented out.
%
%-----K11------
%           tmaix              % Transfer new frame K11 param.
%           tamix              %   to current frame location
%-----K12------
%           tmaix              % Transfer new frame K12 param.
%           tamix              %   to current frame location
%-----
%
% We have now discarded the "current" values by replacing
% them with the "new" values.  We now need to read in
% another frame of speech data and use them as the
% new "new" values
% % % % %
%----- ENERGY -----
            cla
            tcx     FLAGS
            get     EBITS      % get coded energy
            anec    ESILENCE   % Is it a silent frame?
            br      updt0              % no, continue
            orcm    Sil_Flg1 + Int_Inh % yes, set silence flag
            br      ZeroKs             % and zero K params
%
updt0:      anec    ESTOP      % Is it a stop frame?
            br      updt1                     % no, continue
            orcm    STOPFLAG+Sil_Flg1+Int_Inh % yes, set flags
            br      ZeroKs                    % and zero Ks
%
updt1:      acaac   tblen      % add table offset to energy
            luaa               % get decoded energy
            tamd    ENV2       % store the energy in RAM
%
% If this is a silent frame, we are done with the update if
% the previous frame was silent, the new frame should be
% spoken immediately with no ramp up due to interpolation
%
            tcx     FLAGS
            tstcm   Sil_Flg1   % Is this a silent frame?
            br      rtn        %   yes, exit
%
% A repeat frame will use the K parameter from the previous
% frame.  If it is a repeat frame, we need to set a flag.
%
updt2:      get     RBITS      % get the repeat bit
            tstca   #01        % is this a repeat frame?
            br      sflg1      % yes, set repeat flag
            br      updt3

sflg1:      orcm    R_FLAG     % set repeat flag

%----- PITCH -----

updt3:      cla
            get     4          % get coded pitch
            get     3          % get coded petch
            anec    PUnVoiced  % Is the frame unvoiced?
            sbr     updt3a     %   no, continue
            orcm    Unv_Flg1   %   yes, set unvoiced flag

updt3a:     sala               % double coded pitch and
            acaac   tblph      %   add table offset to point

            luab               % get decoded pitch
            iac
            luaa               % get decoded fractional pitch

            tcx     PHV2       % store the pitch and
            tbm                %   fractional pitch in RAM
            ixc
            tam
%
% If the voicing has changed with the new frame, then we
% need to change the voicing in the mode register.
%
            tcx     FLAGS
            tstcm   Unv_Flg1   % Is the new frame unvoiced?
            sbr     updt3b     %   yes, continue
            br      voice      %   no, go to voiced code
%
% The following code is reached if the new frame is
% unvoiced. We inspect the flags to see if the previous
% frame was either silent or voiced. If either condition
% applies, then we branch to code which inhibits
% interpolation.
%
updt3b:     tstcm   Sil_Flg2   % Was the last rame silent?
            br      updt5      %   yes, inhibit interpolation

            tstcm   Unv_Flg2   % Was the last frame unvoiced
            br      updt4      %   yes, don't change anything
            br      updt5      %   no, inhibit interpolation
%
% The following code is reached if the new frame is
% voiced. We inspect the flags to see if the previous
% frame was also voiced. If it was not, we need to inhibit
% interpolation.
%
voice:      tstcm   Unv_Flg2   % Was the last frame voiced?
            br      updt5      %   no, disable interpolation
            br      updt4      %   yes, continue

updt5:      orcm    Int_Inh    % Inhibit interpolation
%
% Now we test the repeat flag. If the new frame is a repeat
% frame, then the current values are used for the K factors,
% so new valunes do not need to be loaded and we can exit the
% routine now.
%
updt4:      tstcm   R_FLAG     % is repeat flag set?
            br      rtn        %   yes, exit routine
%
% Now we need to load the "new" K factors (K1 through K10).
% The first four K factors are 12 bit values which will be
% stored in two bytes. The most significant 8 bits in the
% first byte, and the last significant 4 bits (called the
% fractional value) in the second byte. For K5 through K12,
% the fractional part is assumed to be zero. K11 and K12 are
% no used in LPC10 synthesis, and the code loading them is
% commented out. A coded factor is read into the A
% register. It is then converted to a pointer to a table
% element which contains the uncoded factor. Since the K1
% through K4 table elements consist of two bytes, the
% conversion consists of doubling the coded factor and adding
% the result to the start of the table.  Since the K5 through
% K10 table elements consist of one byte, the coded factor is
% added directly to the start of the table.  Once the pointer
% has been set up, the uncoded factor is fetched and stored
% into RAM.
%
%-----K1-----
            cla
            get     4          % get coded K1
            get     2          % get coded K1
            sala               % convert it to a
            acaac   tblk1      %   pointer to table element
            luab               % fetch MSB of uncoded K1
            iac
            luaa               % fetch fractional K1
            tcx     K1V2
            tbm                % store uncoded K1
            ixc
            tam                % store fractional K1
%-----K2-----
            cla
            get     4          % get coded K2
            get     2          % get coded K2

            sala               % convert it to a
            acaac   tblk2      %   pointer to table element

            luab               % fetch MSB of uncoded K2
            iac
            luaa               % fetch fractional K2
            tcx     K2V2
            tbm                % store uncoded K2
            ixc
            tam                % store fractional K2
%-----K3-----
            cla
            get     4          % get index into K3 table
            get     1          % get index into K3 table
            acaac   tblk3      %   and add offset of table

            luaa               % get uncoded K3
            tamd    K3V2       % and store it in RAM
            cla
            tamd    K3V2+1
%-----K4-----
            cla
            get     4          % get index into K4 table
            get     1          % get index into K4 table
            acaac   tblk4      %   and add offset of table
            luaa               % get uncoded K4
            tamd    K4V2       % and store it in RAM
            cla
            tamd    K4V2+1
%
% If this is an unvoiced frame, we only use four K factors,
% so we load zeros to the rest of the K factors.  If this
% is a voiced frame, load the rest of the uncoded factors.
%
            tcx     FLAGS
            tstcm   Unv_Flg1   % is this an unvoiced frame?
            br      unvc       %   yes, zero rest of factors
%
% The following code si executed if the new frame is
% voiced.  Since we assume that the fractional parameter is
% zero for the remaining K factors, the table elements are
% only one byte long. The conversion to
% a table pointer consists of adding the coded factor to the
% start of the table.
%
%-----K5-----
            cla
            get     K5BITS    % get index into K5 table
            acaac   tblk5     %   and add offset of table

            luaa              % get uncoded K5
            tamd    K5V2      %   and store it in RAM
%-----K6-----
            cla
            get     K6BITS    % get index into K6 table
            acaac   tblk6     %   and add offset of table
            luaa              % get uncoded K6
            tamd    K6V2      %   and store it in RAM
%-----K7-----
            cla
            get     K7BITS    % get index into K7 table
            acaac   tblk7     %   and add offset of table
            luaa              % get uncoded K7
            tamd    K7V2      %   and store it in RAM
%-----K8-----
            cla
            get     K8BITS    % get index into K8 table
            acaac   tblk8     %   and add offset of table
            luaa              % get uncoded K8
            tamd    K8V2      %   and store it in RAM
%-----K9-----
            cla
            get     K9BITS    % get index into K9 table
            acaac   tblk9     %   and add offset of table
            luaa              % get uncoded K9
            tamd    K9V2      %   and store it in RAM
%-----K10-----
            cla
            get     K10BITS   % get index into K10 table
            acaac   tblk10    %   and add offset of table
            luaa              % get uncoded K10
            tamd    K10V2     %   and store it in RAM
%
% Since K11 and K12 are not used in LPC 10, the K11 and K12
% code is commented out.
%
%-----K11-----
%           cla
%           get     K11BITS   % get index into K11 table
%           acaac   tblk11    %   and add offset of table
%           luaa              % get uncoded K11
%           tamd    K11V2     %   and store it in RAM
%-----K12-----
%           cla
%           get     K12BITS   % get index into K12 table
%           acaac   tblk12    %   and add offset of table
%           luaa              % get uncoded K12
%           tamd    K12V2     %   and store it in RAM
%-----
            br      rtn
%
% The following code is executed if the K parameters need to
% be zeroed out.  If the new frame is a stop frame or a
% silent frame, we zero out all K parameters and set the
% energy to zero.  If the new frame is an unvoiced frame,
% then we need to zero out the unused upper K parameters.
%
%
ZeroKs:     cla
            tamd    ENV2      % kill energy
            tamd    K1V2      % kill K1
            tamd    K1V2 + 1
            tamd    K2V2      % kill K2
            tamd    K2V2 + 1
            tamd    K3V2      % kill K3
            tamd    K3V2 + 1
            tamd    K4V2      % kill K4
            tamd    K4V2 + 1
unvc:       cla
            tamd    K5V2      % kill K5
            tamd    K6V2      % kill K6
            tamd    K7V2      % kill K7
            tamd    K8V2      % kill K8
            tamd    K9V2      % kill K9
            tamd    K10V2     % kill K10
%           tamd    K11V2     % kill K11
%           tamd    K12V2     % kill K12
            br      rtn
%
% STOP AND RETURN
%
% The following code has two entry points. STOP is reached
% if the stop flag has been set. It turns off
% synthesis and returns to the program.  RTN is the general
% exit point for the UPDATE routine, it sets the Update flag
% and leaves the routine.
%
stop:       tcx     MODE_BUF
            andcm   ~LPC      % turn off synthesis
            andcm   ~INT1     % disable interrupt
            andcm   ~UNV      % back to voiced for next word
            orcm    PCM       % enable PCM mode
            tma
            tamode            % set mode per above setting
            cla
            tasyn             % write a zero to the DAC
            tca     #F
back:       iac               % wait for a minimum of 30
            br      out       %   instruction cycles
            br      back
out:        tcx     MODE_BUF  % disable PCM
            andcm   ~PCM
            tma
            tamode            % set mode per above setting
            br      speak1    % go back for next word

rtn:        tcx     FLAGS     % set a flag indicating that
            orcm    Update_Flg  % the parameters are updated

            tcx     MODE_BUF  % get mode
            tstcm   LPC       % Are we speking yet?
            br      rtn1      %   yes, re-enable interrupt
            retn              %   no, return for more data

rtn1:       tcx     FLAG1     % inhibit any pending
            orcm    Int_Off   %   interpolation interrupt

            tcx     MODE_BUF  % re-enable the interrupt
            orcm    INT1
            tma
            tamode

            tcx     FLAG1     % re-enable execution
            andcm  ~Int_Off   %   of the interpolation routine
            br      speak_lp  % go back to loop
%
% D6 SPEECH DECODING TABLES.
%
% Energy decoding table
%
tblen:      BYTE    #00,#01,#02,#03,#04,#05,#07,#0b
            BYTE    #11,#1a,#29,#3f,#55,#70,#7f,#00

%
% Pitch period decoding table
%
tblph:      BYTE    #0c,#00
            BYTE    #10,#00
            BYTE    #10,#04
            BYTE    #10,#08
            BYTE    #11,#00
            BYTE    #11,#04
            BYTE    #11,#08
            BYTE    #11,#0c
            BYTE    #12,#04
            BYTE    #12,#08
            BYTE    #12,#0c
            BYTE    #13,#04
            BYTE    #13,#08
            BYTE    #14,#00
            BYTE    #14,#04
            BYTE    #14,#0c
            BYTE    #15,#00
            BYTE    #15,#08
            BYTE    #15,#0c
            BYTE    #16,#04
            BYTE    #16,#0c
            BYTE    #17,#00
            BYTE    #17,#08
            BYTE    #18,#00
            BYTE    #18,#04
            BYTE    #18,#0c
            BYTE    #19,#04
            BYTE    #19,#0c
            BYTE    #1a,#04
            BYTE    #1a,#0c
            BYTE    #1b,#04
            BYTE    #1b,#0c
            BYTE    #1c,#04
            BYTE    #1c,#0c
            BYTE    #1d,#04
            BYTE    #1d,#0c
            BYTE    #1e,#04
            BYTE    #1f,#00
            BYTE    #1f,#08
            BYTE    #20,#00
            BYTE    #20,#0c
            BYTE    #21,#04
            BYTE    #21,#0c
            BYTE    #22,#08
            BYTE    #23,#00
            BYTE    #23,#0c
            BYTE    #24,#08
            BYTE    #25,#00
            BYTE    #25,#0c
            BYTE    #26,#08
            BYTE    #27,#04
            BYTE    #28,#00
            BYTE    #28,#0c
            BYTE    #29,#08
            BYTE    #2a,#04
            BYTE    #2b,#00
            BYTE    #2b,#0c
            BYTE    #2c,#08
            BYTE    #2d,#04
            BYTE    #2e,#04
            BYTE    #2f,#00
            BYTE    #30,#00
            BYTE    #30,#0c
            BYTE    #31,#0c
            BYTE    #32,#08
            BYTE    #33,#08
            BYTE    #34,#08
            BYTE    #35,#08
            BYTE    #36,#08
            BYTE    #37,#08
            BYTE    #38,#08
            BYTE    #39,#08
            BYTE    #3a,#08
            BYTE    #3b,#0c
            BYTE    #3c,#0c
            BYTE    #3d,#0c
            BYTE    #3f,#00
            BYTE    #40,#04
            BYTE    #41,#04
            BYTE    #42,#08
            BYTE    #43,#0c
            BYTE    #45,#00
            BYTE    #46,#04
            BYTE    #47,#08
            BYTE    #49,#00
            BYTE    #4a,#04
            BYTE    #4b,#0c
            BYTE    #4d,#00
            BYTE    #4e,#08
            BYTE    #50,#00
            BYTE    #51,#04
            BYTE    #52,#0c
            BYTE    #54,#08
            BYTE    #56,#00
            BYTE    #57,#08
            BYTE    #59,#04
            BYTE    #5a,#0c
            BYTE    #5c,#08
            BYTE    #5e,#04
            BYTE    #60,#00
            BYTE    #61,#0c
            BYTE    #63,#08
            BYTE    #65,#04
            BYTE    #67,#04
            BYTE    #69,#00
            BYTE    #6b,#00
            BYTE    #6d,#00
            BYTE    #6f,#00
            BYTE    #71,#00
            BYTE    #73,#04
            BYTE    #75,#04
            BYTE    #77,#08
            BYTE    #79,#0c
            BYTE    #7c,#00
            BYTE    #7e,#04
            BYTE    #80,#08
            BYTE    #82,#0c
            BYTE    #85,#04
            BYTE    #87,#0c
            BYTE    #8a,#04
            BYTE    #8c,#0c
            BYTE    #8f,#08
            BYTE    #92,#00
            BYTE    #94,#0c
            BYTE    #97,#08
            BYTE    #9a,#04
            BYTE    #9d,#00
            BYTE    #a0,#00

%
% K1 parameter decoding table
%
tblk1:      BYTE    #81,#00
            BYTE    #82,#04
            BYTE    #83,#04
            BYTE    #84,#08
            BYTE    #85,#0c
            BYTE    #87,#00
            BYTE    #88,#04
            BYTE    #89,#0c
            BYTE    #8b,#04
            BYTE    #8c,#0c
            BYTE    #8e,#04
            BYTE    #90,#00
            BYTE    #91,#0c
            BYTE    #93,#08
            BYTE    #95,#08
            BYTE    #97,#04
            BYTE    #99,#08
            BYTE    #9b,#08
            BYTE    #9d,#08
            BYTE    #9f,#0c
            BYTE    #a2,#00
            BYTE    #a4,#04
            BYTE    #a6,#0c
            BYTE    #a9,#04
            BYTE    #ab,#08
            BYTE    #ae,#00
            BYTE    #b0,#0c
            BYTE    #b3,#08
            BYTE    #b6,#04
            BYTE    #b9,#00
            BYTE    #bc,#00
            BYTE    #bf,#04
            BYTE    #c2,#04
            BYTE    #c5,#08
            BYTE    #c8,#0c
            BYTE    #cc,#04
            BYTE    #cf,#0c
            BYTE    #d3,#08
            BYTE    #d7,#04
            BYTE    #db,#04
            BYTE    #df,#08
            BYTE    #e3,#0c
            BYTE    #e7,#00
            BYTE    #ec,#04
            BYTE    #f0,#04
            BYTE    #f4,#0c
            BYTE    #f9,#0c
            BYTE    #fe,#0c
            BYTE    #04,#04
            BYTE    #09,#0c
            BYTE    #0f,#04
            BYTE    #15,#08
            BYTE    #1c,#08
            BYTE    #23,#08
            BYTE    #2a,#0c
            BYTE    #32,#08
            BYTE    #3a,#08
            BYTE    #42,#0c
            BYTE    #4b,#08
            BYTE    #54,#00
            BYTE    #5c,#04
            BYTE    #65,#00
            BYTE    #6e,#00
            BYTE    #78,#08

%
% K2 parameter decoding table
%
tblk2:      BYTE    #8a,#00
            BYTE    #98,#00
            BYTE    #a3,#0c
            BYTE    #ad,#0c
            BYTE    #b4,#08
            BYTE    #ba,#08
            BYTE    #c0,#00
            BYTE    #c5,#00
            BYTE    #c9,#0c
            BYTE    #ce,#04
            BYTE    #d2,#0c
            BYTE    #d6,#0c
            BYTE    #da,#0c
            BYTE    #de,#08
            BYTE    #e2,#00
            BYTE    #e5,#0c
            BYTE    #e9,#04
            BYTE    #ec,#0c
            BYTE    #f0,#00
            BYTE    #f3,#04
            BYTE    #f6,#08
            BYTE    #f9,#0c
            BYTE    #fd,#00
            BYTE    #00,#00
            BYTE    #03,#04
            BYTE    #06,#04
            BYTE    #09,#04
            BYTE    #0c,#04
            BYTE    #0f,#04
            BYTE    #12,#08
            BYTE    #15,#08
            BYTE    #18,#08
            BYTE    #1b,#08
            BYTE    #1e,#08
            BYTE    #21,#08
            BYTE    #24,#0c
            BYTE    #27,#0c
            BYTE    #2a,#0c
            BYTE    #2d,#0c
            BYTE    #30,#0c
            BYTE    #34,#00
            BYTE    #37,#00
            BYTE    #3a,#04
            BYTE    #3d,#00
            BYTE    #40,#00
            BYTE    #43,#00
            BYTE    #46,#00
            BYTE    #49,#00
            BYTE    #4c,#00
            BYTE    #4f,#04
            BYTE    #52,#04
            BYTE    #55,#04
            BYTE    #58,#04
            BYTE    #5b,#04
            BYTE    #5e,#00
            BYTE    #61,#00
            BYTE    #63,#0c
            BYTE    #66,#08
            BYTE    #69,#04
            BYTE    #6c,#00
            BYTE    #6f,#00
            BYTE    #72,#00
            BYTE    #76,#04
            BYTE    #7c,#00

%
% K3 parameter decoding table
%
tblk3:      BYTE    #8b,#9a,#a2,#a9,#af,#b5,#bb,#c0
            BYTE    #c5,#ca,#cf,#d4,#d9,#de,#e2,#e7
            BYTE    #ec,#f1,#f6,#fb,#01,#07,#0d,#14
            BYTE    #1a,#22,#29,#32,#3b,#45,#53,#6d

%
% K4 parameter decoding table
%
tblk4:      BYTE    #94,#b0,#c2,#cb,#d3,#d9,#df,#e5
            BYTE    #ea,#ef,#f4,#f9,#fe,#03,#07,#0c
            BYTE    #11,#15,#1a,#1f,#24,#29,#2e,#33
            BYTE    #38,#3e,#44,#4b,#53,#5a,#64,#74

%
% K5 parameter decoding table
%
tblk5:      BYTE    #a3,#c5,#d4,#e0,#ea,#f3,#fc,#04
            BYTE    #0c,#15,#1e,#27,#31,#3d,#4c,#66

%
% K6 parameter decoding table
%
tblk6:      BYTE    #aa,#d7,#e7,#f2,#fc,#05,#0d,#14
            BYTE    #1c,#24,#2d,#36,#40,#4a,#55,#6a

%
% K7 parameter decoding table
%
tblk7:      BYTE    #a3,#c8,#d7,#e3,#ed,#f5,#fd,#05
            BYTE    #0d,#14,#1d,#26,#31,#3c,#4b,#67

%
% K8 parameter decoding table
%
tblk8:      BYTE    #c5,#e4,#f6,#05,#14,#27,#3e,#58

%
% K9 parameter decoding table
%
tblk9:      BYTE    #b9,#dc,#ec,#f9,#04,#10,#1f,#45

%
% K10 parameter decoding table
%
tblk10:     BYTE    #c3,#e6,#f3,#fd,#06,#11,#1e,#43


%---------------------------------------------------------%
%                                                         %
%   This is the lookup table given the starting address   %
%   of each concatenation list.                           %
%                                                         %
%---------------------------------------------------------%
sentence:   DATA    phrase0
            DATA    phrase1
            DATA    phrase2
%---------------------------------------------------------%
%                                                         %
%   This is the concatenation table giving the lists      %
%   of word numbers that define each phrase. Each         %
%   list is terminated by an #FF                          %
%                                                         %
%---------------------------------------------------------%
phrase0:    BYTE    1,2,3,4,#FF
phrase1:    BYTE    4,3,2,1,#FF
phrase2:    BYTE    5,4,3,2,1,#FF
%---------------------------------------------------------%
%                                                         %
%   This is the lookup table for the speech stored at     %
%   voc.                                                  %
%                                                         %
%---------------------------------------------------------%
speech:     DATA    #0000
            DATA    #0000 + voc % Word 1 "One"
            DATA    #0084 + voc % Word 2 "Two"
            DATA    #00f6 + voc % Word 3 "Three"
            DATA    #017a + voc % Word 4 "Four"
            DATA    #01e0 + voc % Word 5 "Five"
            DATA    #028c + voc % Word 6 "Six"
%---------------------------------------------------------%
%                                                         %
%   This is the DTS speech coded with the D6 coding       %
%   table                                                 %
%                                                         %
%---------------------------------------------------------%
voc:
            BYTE    #68,#89,#84,#fb,#1a,#53,#64,#b2
            BYTE    #84,#87,#33,#c9,#35,#28,#9b,#a1
            BYTE    #d1,#ba,#22,#3a,#94,#8d,#08,#bd
            BYTE    #be,#40,#1c,#6d,#ba,#bc,#14,#7e
            BYTE    #33,#ce,#4e,#75,#8d,#ee,#2f,#03
            BYTE    #bb,#96,#4a,#46,#d7,#cf,#4a,#dd
            BYTE    #4a,#23,#54,#ce,#26,#b7,#74,#a5
            BYTE    #9b,#49,#7b,#62,#44,#b7,#32,#2d
            BYTE    #95,#d9,#c8,#b4,#5b,#9a,#35,#5a
            BYTE    #8d,#c2,#dc,#2c,#cc,#5a,#cc,#0a
            BYTE    #2b,#6e,#ee,#66,#19,#69,#98,#27
            BYTE    #75,#33,#cb,#80,#36,#ac,#94,#e6
            BYTE    #a9,#85,#ce,#4b,#1b,#ec,#cd,#d4
            BYTE    #2c,#50,#71,#52,#f5,#76,#aa,#1b
            BYTE    #9b,#38,#98,#58,#33,#56,#b6,#35
            BYTE    #d2,#58,#a3,#99,#c8,#7b,#ae,#d5
            BYTE    #a8,#5e,#fb,#01,#04,#b0,#78,#ba
            BYTE    #2b,#c0,#5d,#1b,#6d,#00,#f7,#65
            BYTE    #ba,#01,#64,#ba,#13,#29,#b7,#06
            BYTE    #36,#81,#c9,#fe,#92,#db,#5c,#15
            BYTE    #20,#b8,#7f,#29,#af,#8a,#ca,#10
            BYTE    #dc,#3f,#35,#12,#56,#47,#2a,#fa
            BYTE    #9f,#fa,#26,#61,#97,#0c,#ed,#77
            BYTE    #43,#9a,#6e,#97,#9a,#f7,#8a,#01
            BYTE    #2e,#ce,#8d,#29,#7b,#48,#17,#b1
            BYTE    #cf,#86,#b4,#4e,#64,#04,#47,#77
            BYTE    #a1,#4b,#26,#32,#83,#9b,#13,#31
            BYTE    #ad,#23,#59,#e3,#da,#5e,#90,#b2
            BYTE    #85,#ac,#68,#65,#0d,#70,#e9,#4d
            BYTE    #36,#44,#38,#13,#87,#74,#12,#bb
            BYTE    #8d,#52,#59,#90,#e4,#3d,#08,#60
            BYTE    #ca,#86,#13,#40,#66,#1a,#46,#00
            BYTE    #b9,#ec,#8b,#00,#14,#59,#b7,#0a
            BYTE    #90,#5a,#35,#9a,#ec,#1e,#d9,#86
            BYTE    #a4,#ea,#5c,#41,#69,#85,#b2,#a6
            BYTE    #ee,#21,#af,#cc,#24,#46,#63,#f7
            BYTE    #94,#53,#26,#e1,#65,#b1,#7b,#c9
            BYTE    #3b,#a5,#77,#b8,#92,#3e,#e5,#9b
            BYTE    #b4,#7b,#18,#ee,#9f,#0a,#5b,#52
            BYTE    #02,#b4,#ee,#4f,#8d,#23,#cf,#06
            BYTE    #2a,#b7,#a7,#fe,#96,#04,#0a,#dd
            BYTE    #df,#d2,#70,#b6,#24,#c6,#9d,#25
            BYTE    #61,#3c,#f0,#1c,#f3,#ed,#a4,#30
            BYTE    #59,#74,#8e,#70,#e7,#96,#9b,#4c
            BYTE    #0a,#47,#74,#3b,#d1,#cc,#07,#95
            BYTE    #21,#be,#19,#65,#a6,#b3,#27,#20
            BYTE    #ce,#4c,#62,#93,#58,#41,#b4,#77
            BYTE    #0a,#3e,#80,#00,#a6,#6a,#03,#01
            BYTE    #54,#a6,#4f,#0c,#10,#c6,#d1,#0b
            BYTE    #80,#97,#d4,#e0,#12,#2a,#d7,#37
            BYTE    #87,#58,#09,#e9,#18,#b7,#3f,#0d
            BYTE    #bd,#87,#74,#8a,#99,#9f,#86,#de
            BYTE    #43,#d9,#26,#ea,#37,#c5,#ec,#a1
            BYTE    #a9,#b0,#f3,#91,#71,#fe,#30,#60
            BYTE    #83,#b3,#b1,#c4,#7f,#1a,#b3,#ed
            BYTE    #8e,#d4,#a2,#3f,#cc,#84,#ad,#4a
            BYTE    #1b,#e8,#1f,#d6,#ea,#38,#a4,#1c
            BYTE    #e6,#0f,#5b,#63,#49,#d4,#0f,#f3
            BYTE    #b9,#83,#b1,#7b,#e2,#87,#7b,#dd
            BYTE    #d5,#ba,#a8,#e8,#c5,#5d,#0f,#00
            BYTE    #08,#90,#fb,#51,#23,#80,#ab,#19
            BYTE    #4a,#00,#b9,#97,#0d,#01,#34,#59
            BYTE    #49,#0c,#d0,#a5,#29,#11,#80,#e5
            BYTE    #86,#58,#ea,#be,#32,#36,#27,#f5
            BYTE    #69,#b5,#4c,#18,#cb,#9b,#da,#b5
            BYTE    #7a,#aa,#ec,#61,#45,#6b,#4b,#33
            BYTE    #f0,#6f,#d1,#94,#25,#a5,#ed,#15
            BYTE    #37,#68,#ea,#9c,#d4,#75,#ba,#ed
            BYTE    #34,#6d,#4e,#19,#7b,#cd,#76,#9a
            BYTE    #7a,#bb,#cc,#a2,#f2,#18,#4d,#b9
            BYTE    #59,#96,#59,#71,#b4,#a4,#3c,#2a
            BYTE    #cb,#bc,#5a,#5c,#52,#67,#a6,#4d
            BYTE    #36,#36,#aa,#61,#17,#d3,#2e,#6f
            BYTE    #22,#93,#f4,#05,#61,#1f,#56,#52
            BYTE    #69,#e7,#41,#b3,#0f,#32,#e1,#ac
            BYTE    #e2,#b0,#d9,#eb,#95,#34,#5c,#7e
            BYTE    #52,#ec,#e5,#44,#1b,#4a,#79,#c1
            BYTE    #f6,#3a,#6d,#1c,#9a,#76,#66,#bb
            BYTE    #51,#32,#16,#89,#94,#99,#dd,#96
            BYTE    #8f,#69,#c9,#6a,#d5,#6e,#f2,#52
            BYTE    #21,#62,#6a,#62,#37,#24,#2d,#22
            BYTE    #11,#97,#07,#00,#04,#f0,#2a,#08
            BYTE    #13,#c0,#bf,#f9,#44,#00,#ff,#ee
            BYTE    #95,#00,#7c,#a5,#d3,#02,#f0,#b5
            BYTE    #da,#94,#62,#c6,#17,#8d,#d9,#b7
            BYTE    #4b,#be,#97,#8b,#25,#cb,#d7,#a5
            BYTE    #5a,#aa,#4d,#72,#f7,#db,#d4,#2f
            BYTE    #bd,#4c,#75,#ea,#6b,#5a,#84,#15
            BYTE    #d1,#dd,#bd,#11,#00,#80,#01,#1c
            BYTE    #6f,#6b,#01,#78,#ac,#be,#05,#e0
            BYTE    #5f,#75,#62,#80,#7f,#d0,#9d,#01
            BYTE    #be,#8f,#7b,#02,#78,#3b,#5d,#1e
            BYTE    #08,#f0,#15,#3e,#13,#c0,#57,#f3
            BYTE    #4c,#00,#7f,#cf,#38,#01,#fc,#81
            BYTE    #32,#0c,#f0,#5f,#c2,#85,#62,#c5
            BYTE    #0d,#85,#59,#9b,#5a,#25,#d5,#87
            BYTE    #a4,#aa,#67,#a5,#5a,#04,#5b,#62
            BYTE    #d7,#dc,#52,#4b,#9a,#c9,#a9,#f2
            BYTE    #49,#e9,#46,#6d,#37,#94,#fe,#c4
            BYTE    #8c,#75,#b3,#58,#52,#cb,#64,#a6
            BYTE    #2c,#53,#23,#47,#a6,#35,#6b,#de
            BYTE    #c8,#9a,#23,#6b,#a5,#55,#e0,#36
            BYTE    #c9,#1a,#b7,#d2,#3e,#0e,#26,#67
            BYTE    #8d,#4b,#66,#af,#26,#99,#bb,#d5
            BYTE    #40,#b5,#97,#2d,#36,#95,#3a,#e6
            BYTE    #03,#00,#a6,#2a,#5a,#be,#d6,#45
            BYTE    #e8,#50,#c9,#5c,#a9,#ec,#7a,#76
            BYTE    #a9,#8c,#91,#65,#b8,#fd,#b6,#54
            BYTE    #d6,#3c,#52,#ac,#d9,#5a,#8a,#9b
            BYTE    #e9,#11,#6d,#3f,#2d,#e5,#29,#96
            BYTE    #50,#ae,#e7,#a6,#fe,#92,#2b,#28
            BYTE    #75,#ab,#dd,#a6,#8f,#29,#d4,#d9
            BYTE    #59,#00,#0c,#b0,#08,#d4,#0a,#c0
            BYTE    #13,#e6,#ae,#00,#6b,#7d,#9b,#02
            BYTE    #8c,#e5,#32,#0f,#a4,#25,#53,#73
            BYTE    #57,#50,#53,#d1,#93,#c5,#3c,#5b
            BYTE    #65,#99,#18,#ca,#7c,#99,#65,#bc
            BYTE    #ce,#8d,#65,#4a,#0f,#4d,#9d,#53
            BYTE    #c6,#9e,#d3,#1c,#65,#4e,#2c,#23
            BYTE    #3f,#3b,#52,#d2,#4f,#95,#9e,#9f
            BYTE    #1d,#29,#e9,#a7,#4a,#37,#b7,#4f
            BYTE    #a5,#b2,#35,#a5,#9b,#db,#a7,#52
            BYTE    #d9,#9a,#d2,#c9,#93,#93,#a8,#74
            BYTE    #4d,#e9,#96,#d9,#f2,#54,#b2,#ba
            BYTE    #8c,#f2,#ba,#09,#69,#9d,#59,#46
            BYTE    #65,#1e,#99,#96,#56,#4c,#a3,#38
            BYTE    #54,#cc,#5b,#0b,#b9,#91,#ad,#1b
            BYTE    #9e,#c5,#45,#d9,#18,#73,#c2,#0c

% EXCITATION FUNCTION
            
            AORG    #4000
            BYTE    #00,#a2,#00,#af,#00,#ba,#00,#c2
            BYTE    #00,#c7,#00,#c9,#00,#ca,#00,#c6
            BYTE    #00,#c2,#00,#bc,#00,#b5,#00,#ad
            BYTE    #00,#a5,#00,#9e,#00,#9a,#00,#95
            BYTE    #00,#95,#00,#98,#00,#9f,#00,#a8
            BYTE    #00,#b8,#00,#ca,#00,#e3,#00,#fe
            BYTE    #01,#1f,#01,#41,#01,#69,#01,#91
            BYTE    #01,#bd,#01,#e8,#02,#16,#02,#40
            BYTE    #02,#6c,#02,#92,#02,#b9,#02,#d9
            BYTE    #02,#f8,#03,#0f,#03,#25,#03,#32
            BYTE    #03,#3f,#03,#43,#03,#47,#03,#45
            BYTE    #03,#45,#03,#3f,#03,#3d,#03,#3a
            BYTE    #03,#3d,#03,#41,#03,#4e,#03,#5f
            BYTE    #03,#7b,#03,#a0,#03,#d2,#04,#0d
            BYTE    #04,#57,#04,#ad,#05,#11,#05,#82
            BYTE    #06,#00,#06,#8a,#07,#1f,#07,#bd
            BYTE    #08,#64,#09,#11,#09,#c1,#0a,#74
            BYTE    #0b,#26,#0b,#d5,#0c,#7f,#0d,#20
            BYTE    #0d,#b7,#0e,#40,#0e,#bb,#0f,#24
            BYTE    #0f,#7a,#0f,#bc,#0f,#e9,#0f,#ff
            BYTE    #0f,#ff,#0f,#e9,#0f,#bc,#0f,#7a
            BYTE    #0f,#24,#0e,#bb,#0e,#40,#0d,#b7
            BYTE    #0d,#20,#0c,#7f,#0b,#d5,#0b,#26
            BYTE    #0a,#74,#09,#c1,#09,#11,#08,#64
            BYTE    #07,#bd,#07,#1f,#06,#8a,#06,#00
            BYTE    #05,#82,#05,#11,#04,#ad,#04,#57
            BYTE    #04,#0d,#03,#d2,#03,#a0,#03,#7b
            BYTE    #03,#5f,#03,#4e,#03,#41,#03,#3d
            BYTE    #03,#3a,#03,#3d,#03,#3f,#03,#45
            BYTE    #03,#45,#03,#47,#03,#43,#03,#3f
            BYTE    #03,#32,#03,#25,#03,#0f,#02,#f8
            BYTE    #02,#d9,#02,#b9,#02,#92,#02,#6c
            BYTE    #02,#40,#02,#16,#01,#e8,#01,#bd
            BYTE    #01,#91,#01,#69,#01,#41,#01,#1f
            BYTE    #00,#fe,#00,#e3,#00,#ca,#00,#b8
            BYTE    #00,#a8,#00,#9f,#00,#98,#00,#95
            BYTE    #00,#95,#00,#9a,#00,#9e,#00,#a5
            BYTE    #00,#ad,#00,#b5,#00,#bc,#00,#c2
            BYTE    #00,#c6,#00,#ca,#00,#c9,#00,#c7
            BYTE    #00,#c2,#00,#ba,#00,#af,#00,#a2
            BYTE    #05,#80,#05,#80,#05,#80,#05,#80
            BYTE    #05,#80,#05,#80,#05,#80,#05,#80
            BYTE    #05,#80,#05,#80,#05,#80,#05,#80
            BYTE    #05,#80,#05,#80,#05,#80,#05,#80
            BYTE    #3a,#80,#3a,#80,#3a,#80,#3a,#80
            BYTE    #3a,#80,#3a,#80,#3a,#80,#3a,#80
            BYTE    #3a,#80,#3a,#80,#3a,#80,#3a,#80
            BYTE    #3a,#80,#3a,#80,#3a,#80,#3a,#80
%           BYTE    #ff,#ff,#ff,#ff,#ff,#ff,#ff,#ff
%           BYTE    #ff,#ff,#ff,#ff,#ff,#ff,#ff,#ff
%           BYTE    #ff,#ff,#ff,#ff,#ff,#ff,#ff,#ff
%           BYTE    #ff,#ff,#ff,#ff,#ff,#ff,#ff,#ff
%           BYTE    #ff,#ff,#ff,#ff,#ff,#ff,#ff,#ff
%           BYTE    #ff,#ff,#ff,#ff,#ff,#ff,#ff,#ff
%           BYTE    #ff,#ff,#ff,#ff,#ff,#ff,#ff,#ff
%           BYTE    #ff,#ff,#ff,#ff,#ff,#ff,#ff,#ff
%           BYTE    #ff,#ff,#ff,#ff,#ff,#ff,#ff,#ff
%           BYTE    #ff,#ff,#ff,#ff,#ff,#ff,#ff,#ff
