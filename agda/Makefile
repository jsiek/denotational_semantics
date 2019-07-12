%.agdai: %.agda
	agda  $<

#	BelowBCDConst.agda \
#	FunInverseBCDConst.agda \
#	CurryBCDConst.agda \

AGDA = Variables.agda \
	Primitives.agda \
	Structures.agda \
	ValueConst.agda \
	Syntax3.agda \
	MultiStep.agda \
	ValueStructAux.agda \
	OrderingAux.agda \
	Consistency.agda \
	ConsistentAux.agda \
	CurryConst.agda \
	PrimConst.agda \
	ModelCurryConst.agda \
	WFDenotMod.agda \
	CurryApplyStruct.agda \
	CurryApplyAux.agda \
	ISWIMDenot.agda \
	ISWIMDenotAlt.agda \
	Compositionality.agda \
	ValueBCD.agda \
	LambdaDenot.agda \
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
