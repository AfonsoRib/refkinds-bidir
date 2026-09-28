"""Regenerate reviewed semantic-coverage mappings for historical evidence.

The original command files and the implementation-v1 catalogue are immutable
evidence. This script records which independently authored current-language
scenario exercises each behavior; it never translates historical source.
"""

import json
import re
from pathlib import Path

import yaml


FIXTURES = [
    ("a.rk", "resources/fixtures/original/refK/a.rk"),
    ("my_examples.rk", "resources/fixtures/original/refK_artifact/my_examples.rk"),
    ("fun_and_rec.rk", "resources/fixtures/original/refK_artifact/fun_and_rec.rk"),
    ("larger_examples.rk", "resources/fixtures/original/refK_artifact/larger_examples.rk"),
    ("paper_examples.rk", "resources/fixtures/original/refK_artifact/paper_examples.rk"),
    ("small_examples.rk", "resources/fixtures/original/refK_artifact/small_examples.rk"),
    ("map_eval_tests.rk", "resources/fixtures/original/refK_artifact/map_eval_tests.rk"),
]


GROUP_SCENARIOS = {
    "testANF": "syntax.anf",
    "testAlphaEquivalence": "syntax.locally-nameless",
    "testAnnotationsAndForall": "types.polymorphic",
    "testArrow": "types.specialised",
    "testBindings": "terms.bindings",
    "testBoolean": "terms.primitives",
    "testBooleanOperations": "conditionals.guarded",
    "testBranchDefinitionalEquality": "definitions.conversion",
    "testCheckerBinderHygiene": "syntax.locally-nameless",
    "testCollections": "types.specialised",
    "testConditionals": "conditionals.guarded",
    "testDefinitionalEquality": "definitions.conversion",
    "testDesugar": "syntax.lowering",
    "testFalse": "terms.primitives",
    "testFunAndRecExamples": "records.add-field",
    "testGeneratedProperties": "records.apartness",
    "testInteger": "terms.primitives",
    "testKnownLanguageBoundaries": "recursion.rejection",
    "testLabel": "types.singleton",
    "testLargerExamples": "records.merge",
    "testLexicalAndAtomicSyntax": "syntax.parser",
    "testLocallyNameless": "syntax.locally-nameless",
    "testMapEvaluationExamples": "paper.map",
    "testPaperExamples": "paper.proj",
    "testPaperPairAndMapSpecializations": "paper.map",
    "testPaperRecordAndFunctionExamples": "paper.mktable",
    "testPaperTermExamples": "paper.gtype",
    "testParseErrors": "syntax.rejection",
    "testParsedPrograms": "syntax.modules",
    "testParsedRecords": "syntax.parser",
    "testParsedTerms": "syntax.parser",
    "testPiKinds": "types.dependent-pi",
    "testPredicateTraversal": "refinements.predicates",
    "testPredicates": "refinements.predicates",
    "testRecordInvariantExamples": "records.invariants",
    "testRecords": "records.freshness",
    "testReferences": "types.specialised",
    "testRefinedBaseKindIfExamples": "conditionals.guarded",
    "testRowConcatIdentity": "records.merge",
    "testRows": "records.merge",
    "testSelectors": "records.selectors",
    "testShortCircuitRefinement": "refinements.contradiction",
    "testSmallExamples": "types.singleton",
    "testStructuralUtilities": "recursion.structural",
    "testSubkindingAndSolver": "refinements.subkinding",
    "testSymbolicRows": "records.symbolic",
    "testTermConditionals": "conditionals.guarded",
    "testTermCore": "terms.core",
    "testTermEvaluation": "terms.evaluation",
    "testTermFunctions": "terms.functions",
    "testTermLets": "terms.bindings",
    "testTermMap": "paper.map",
    "testTermPolymorphism": "types.polymorphic",
    "testTermRecords": "records.terms",
    "testTrue": "terms.primitives",
    "testTypeApplication": "types.dependent-pi",
    "testTypeEvaluation": "definitions.conversion",
    "testTypeLambda": "types.dependent-pi",
    "testTypesAndKinds": "types.singleton",
    "testUnit": "terms.primitives",
}


SCENARIOS = {
    "syntax.anf": "ANF",
    "syntax.locally-nameless": "Locally Nameless",
    "syntax.lowering": "Surface lowering",
    "syntax.parser": "Parser",
    "syntax.modules": "Parser",
    "syntax.rejection": "Parser",
    "terms.core": "Term Checker",
    "terms.primitives": "Evaluation",
    "terms.bindings": "Evaluation",
    "terms.evaluation": "Evaluation",
    "terms.functions": "Term Checker",
    "types.singleton": "Refinement semantic scenarios",
    "types.dependent-pi": "Refinement semantic scenarios",
    "types.specialised": "Refinement semantic scenarios",
    "types.polymorphic": "Refinement semantic scenarios",
    "definitions.conversion": "Definitional Equality",
    "conditionals.guarded": "Kind cases",
    "refinements.predicates": "Type Checker",
    "refinements.contradiction": "Refinement semantic scenarios",
    "refinements.subkinding": "Subkinding",
    "records.add-field": "Refinement semantic scenarios",
    "records.apartness": "Refinement semantic scenarios",
    "records.freshness": "Record constraint generation",
    "records.invariants": "Record constraint generation",
    "records.merge": "Refinement semantic scenarios",
    "records.selectors": "Refinement semantic scenarios",
    "records.symbolic": "Record constraint generation",
    "records.terms": "Record constraint generation",
    "paper.proj": "Refinement semantic scenarios",
    "paper.map": "Recursive refined Map",
    "paper.gtype": "Canonical Fixtures and Manifest",
    "paper.mktable": "Canonical Fixtures and Manifest",
    "recursion.structural": "Recursive refined Map",
    "recursion.rejection": "Refinement semantic scenarios",
    "rejection.static": "Refinement semantic scenarios",
}


def split_commands(text):
    return [chunk.strip() for chunk in text.split(";;") if chunk.strip()]


def normalize_command(command):
    return re.sub(r"\s+", " ", command).strip()


def scenario_for_command(command):
    text = command.lower()
    if "mktable" in text or "xform" in text:
        return "paper.mktable"
    if "gtype" in text or "genconstr" in text:
        return "paper.gtype"
    if "proj" in text:
        return "paper.proj"
    if "map" in text:
        return "paper.map"
    if "addfield" in text:
        return "records.add-field"
    if " # " in text:
        return "records.apartness"
    if " inl " in text or "labset" in text:
        return "records.invariants"
    if any(selector in text for selector in ("head(", "head (", "headlb", "tail(")):
        return "records.selectors"
    if "if " in text:
        return "conditionals.guarded"
    if "ref " in text or "refof" in text:
        return "types.specialised"
    if "all " in text:
        return "types.polymorphic"
    if "letrec" in text:
        return "recursion.structural"
    if "pi " in text or "fun " in text:
        return "types.dependent-pi"
    if "[|" in text or "[`" in text:
        return "records.terms"
    if "{" in text and "|" in text:
        return "types.singleton"
    return "terms.core"


def historical_disposition(command):
    normalized = normalize_command(command)
    lowered = normalized.lower()
    if lowered == "quit" or "end of file" in lowered or lowered.startswith("//"):
        return {"status": "non-test", "reason": "historical sentinel or commented command"}
    if ("fails on purpose" in lowered
            or "((fun y:bool => y) y)" in lowered
            or "fun t::rec -> { t :: rec | ~ empty(s)" in lowered):
        return {"status": "expected-rejection", "scenario_id": "rejection.static"}
    if re.search(r"\btop\b", lowered):
        return {"status": "unsupported", "reason": "the current language intentionally has no Top term type"}
    if re.search(r"\d+\s*\*", lowered):
        return {"status": "unsupported", "reason": "integer arithmetic primitives are outside the current language"}
    return {"status": "covered", "scenario_id": scenario_for_command(command)}


def write_historical_manifest():
    entries = []
    first_occurrence = {}
    for module_file, evidence_path in FIXTURES:
        commands = split_commands(Path(evidence_path).read_text())
        for index, command in enumerate(commands, start=1):
            disposition = historical_disposition(command)
            normalized = normalize_command(command)
            if disposition["status"] == "covered" and normalized in first_occurrence:
                disposition = {
                    "status": "duplicate",
                    "scenario_id": disposition["scenario_id"],
                    "duplicate_of": first_occurrence[normalized],
                }
            elif disposition["status"] == "covered":
                first_occurrence[normalized] = f"{module_file}:{index}"
            entries.append({
                "file": module_file,
                "index": index,
                "original": command,
                "module_file": module_file,
                **disposition,
            })
    manifest = {"schema": 2, "total_commands": len(entries), "manifest": entries}
    Path("test/fixtures/manifest.yaml").write_text(
        yaml.safe_dump(manifest, sort_keys=False), encoding="utf-8"
    )
    Path("test/fixtures/manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )


def write_v1_mapping():
    catalogue = yaml.safe_load(Path("resources/tests/implementation-v1-behaviors.yaml").read_text())
    mappings = []
    for behavior in catalogue["behaviors"]:
        status = "expected-rejection" if behavior["expected"] == "reject" else "covered"
        mappings.append({
            "behavior_id": behavior["id"],
            "classification": behavior["classification"],
            "status": status,
            "scenario_id": "rejection.static" if status == "expected-rejection" else GROUP_SCENARIOS[behavior["group"]],
        })
    target = Path("test/coverage")
    target.mkdir(parents=True, exist_ok=True)
    (target / "implementation-v1-scenarios.json").write_text(
        json.dumps({"schema": 1, "behavior_count": len(mappings), "mappings": mappings}, indent=2) + "\n",
        encoding="utf-8",
    )
    (target / "scenarios.json").write_text(
        json.dumps({"schema": 1, "scenarios": [
            {"id": scenario_id, "test_group": test_group}
            for scenario_id, test_group in sorted(SCENARIOS.items())
        ]}, indent=2) + "\n",
        encoding="utf-8",
    )


write_historical_manifest()
write_v1_mapping()
print("Recorded historical commands and implementation-v1 scenario mappings.")
