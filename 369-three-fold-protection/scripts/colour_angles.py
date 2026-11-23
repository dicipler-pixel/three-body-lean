# SCRIPT: SM369-COLOUR-ANGLES — digit sums of the Mixin/polarizer angles in degrees vs other angle units
from fractions import Fraction
def dsum(x):  # digit sum of a terminating decimal, decimal point ignored
    s = format(x, 'f').rstrip('0').rstrip('.') if isinstance(x, float) else str(x)
    return sum(int(c) for c in s if c.isdigit())
ang = [Fraction(225, 10)*k for k in range(1, 16)]
print('kill condition: if the digit-sum-9 property survives a change of angle unit, it is physical; if it changes, it belongs to the degree convention (360 = 2^3·3^2·5)')
print('degrees      :', [float(a) for a in ang])
print('digit sums mod 9 (degrees):', [dsum(float(a)) % 9 for a in ang])
grad = [a*Fraction(400, 360) for a in ang]; print('gradians     :', [float(g) for g in grad]); print('digit sums mod 9 (gradians):', [dsum(float(g)) % 9 for g in grad])
turns = [a/360 for a in ang]; print('turns        :', [float(t) for t in turns]); print('digit sums mod 9 (turns):', [dsum(float(t)) % 9 for t in turns])
print('reason: 360 = 2^3·3^2·5, and k·360/16 = 22.5·k = 9·(2.5k); halving in decimal multiplies the digit string by 5, which keeps divisibility by 9')
