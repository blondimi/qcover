vars
unlockS lockS unlockC lockC Swhile Sbefore Sbad Sin Safterin Send Cwhile Cbefore Cbad Cin Cafterin Cend

rules
#saving
Swhile >= 1 ->
	Swhile' = Swhile - 1,
	Sbefore' = Sbefore + 1;

Sbefore >= 1, unlockS >= 1 ->
	Sbefore' = Sbefore - 1,
	Sbad' = Sbad + 1,
	unlockS' = unlockS - 1,
	lockS' = lockS + 1;

Sbad >= 1, unlockC >= 1 ->
	Sbad' = Sbad - 1,
	Sin' = Sin + 1,
	unlockC' = unlockC - 1,
	lockC' = lockC + 1;

Sin >= 1, lockC >= 1 ->
	Sin' = Sin - 1,
	Safterin' = Safterin + 1,
	lockC' = lockC - 1,
	unlockC' = unlockC + 1;

Safterin >=1, lockS >= 1 ->
	Safterin' = Safterin - 1,
	Send' = Send + 1,
	lockS' = lockS - 1,
	unlockS' = unlockS + 1;

Send >= 1 ->
	Send' = Send - 1,
	Swhile' = Swhile + 1;

#checking
Cwhile >= 1 ->
        Cwhile' = Cwhile - 1,
        Cbefore' = Cbefore + 1;

Cbefore >= 1, unlockC >= 1 ->
        Cbefore' = Cbefore - 1,
        Cbad' = Cbad + 1,
        unlockC' = unlockC - 1,
        lockC' = lockC + 1;

Cbad >= 1, unlockS >= 1 ->
        Cbad' = Cbad - 1,
        Cin' = Cin + 1,
        unlockS' = unlockS - 1,
        lockS' = lockS + 1;

Cin >= 1, lockS >= 1 ->
        Cin' = Cin - 1,
        Cafterin' = Cafterin + 1,
        lockS' = lockS - 1,
        unlockS' = unlockS + 1;

Cafterin >=1, lockC >= 1 ->
        Cafterin' = Cafterin - 1,
        Cend' = Cend + 1,
        lockC' = lockC - 1,
        unlockC' = unlockC + 1;

Cend >= 1 ->
	Cend' = Cend - 1,
	Cwhile' = Cwhile + 1;


init
unlockS = 1 , lockS = 0 , unlockC = 1 , lockC = 0 , Swhile >= 1, Sbefore = 0 , Sbad = 0 , Sin = 0 , Safterin = 0 , Send = 0 , Cwhile >= 1 , Cbefore = 0 , Cbad = 0 , Cin = 0 , Cafterin = 0 , Cend = 0

target
Sbad >= 1 , Cbad >= 1

invariants
unlockS = 1, lockS = 1
unlockC = 1, lockC = 1
unlockS = 1, Sbad = 1, Sin = 1, Safterin = 1, Cin = 1
unlockC = 1, Sin  = 1, Cbad = 1, Cin = 1, Cafterin = 1
