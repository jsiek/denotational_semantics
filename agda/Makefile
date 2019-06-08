%.agdai: %.agda
	agda  $<

AGDA = Variables.agda \
	Syntax2.agda \
	Primitives.agda \
	Structures.agda \
	MultiStep.agda \
	ValueBCD.agda \
	ValueBCDConst.agda \
	BelowBCDConst.agda \
	FunInverseBCDConst.agda \
	CurryBCDConst.agda \
	Consistency.agda \
	Lambda.agda \
	LambdaCallByValue.agda \
	ISWIM.agda \
	EvalCallByName.agda \
	EvalCallByValue.agda \
	EvalISWIM.agda \
	ModelCallByName.agda \
	ModelCallByValue.agda \
	ModelISWIM.agda \
	RenamePreserveReflect.agda \
	Filter.agda \
	SubstitutionPreserve.agda \
	SubstitutionReflect.agda \
	SoundnessCallByName.agda \
	SoundnessCallByValue.agda \
	SoundnessISWIM.agda \
	AdequacyCallByName.agda \
	AdequacyCallByValue.agda \
	AdequacyISWIM.agda 

AGDAI = $(AGDA:%.agda=%.agdai)

all: ${AGDA} ${AGDAI}

clean:
	rm -f *.agdai *~
