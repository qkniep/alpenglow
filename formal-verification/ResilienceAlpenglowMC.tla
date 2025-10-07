---------------------------- MODULE ResilienceAlpenglowMC -----------------------------
EXTENDS ResilienceAlpenglow

AllValidators == {"v1", "v2", "v3", "v4", "v5"}
ByzantineValidators == {"v1"}  \* 20% of 5 validators = 1 Byzantine
CrashedValidators == {"v2"}    \* 20% of 5 validators = 1 crashed
MaxSlot == 3
TotalStake == 100

=============================================================================