"""Artifact registry recovery and fresh-process reconstruction in Macaulay2."""

from __future__ import annotations

import json
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from pathlib import Path
from unittest.mock import patch

from batch.records import ArtifactError, ArtifactStore, model_digest, read_artifact_json

from ..helpers import MODEL, body


class ArtifactRegistry(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.store = ArtifactStore(Path(temporary.name))

    def test_interruption_and_concurrent_publication(self) -> None:
        expected = sha256(body(MODEL)).hexdigest()
        self.store.objects.mkdir()
        (self.store.objects / ".part-crash").write_bytes(b"partial")
        with (
            patch("batch.records.artifacts.os.link", side_effect=OSError("link interrupted")),
            self.assertRaisesRegex(OSError, "link interrupted"),
        ):
            self.store.publish(MODEL, "interrupted-before-link")
        self.assertFalse((self.store.objects / f"{expected}.json").exists())
        publish_file = self.store._publish_file

        def stop_after_link(digest: str, content: bytes) -> None:
            publish_file(digest, content)
            raise KeyboardInterrupt

        with (
            patch.object(self.store, "_publish_file", side_effect=stop_after_link),
            self.assertRaises(KeyboardInterrupt),
        ):
            self.store.publish(MODEL, "interrupted-before-registration")
        self.assertEqual((self.store.objects / f"{expected}.json").read_bytes(), body(MODEL))
        with self.assertRaisesRegex(ArtifactError, "not registered"):
            self.store.read(expected)

        with ThreadPoolExecutor(max_workers=2) as pool:
            results = list(pool.map(lambda attempt: self.store.publish(MODEL, attempt), ("first", "second")))
        self.assertEqual(results, [expected, expected])
        self.assertEqual(self.store.publish(MODEL, "first"), expected)
        self.assertEqual(self.store.read(expected), body(MODEL))
        connection = sqlite3.connect(self.store.database)
        try:
            self.assertEqual(
                connection.execute("SELECT * FROM artifact").fetchall(),
                [(expected, len(body(MODEL)), 1, "k3-model", None)],
            )
            self.assertEqual(
                connection.execute("SELECT attempt FROM producer ORDER BY attempt").fetchall(),
                [("first",), ("second",)],
            )
        finally:
            connection.close()
        self.assertEqual(
            sorted(p.name for p in self.store.objects.iterdir()), [".part-crash", f"{expected}.json"]
        )

    def test_damaged_model_and_wrong_parent_kind(self) -> None:
        digest = self.store.publish(MODEL, "run")
        presentation = {
            "version": 1,
            "kind": "graded-presentation",
            "payload": {"model_digest": digest, "source": [], "target": [], "matrix": []},
        }
        presentation_digest = self.store.publish(presentation, "run")
        self.assertEqual(self.store.read(presentation_digest), body(presentation))
        presentation["payload"]["model_digest"] = presentation_digest
        with self.assertRaisesRegex(ArtifactError, "not a K3 model"):
            self.store.publish(presentation, "run")
        (self.store.objects / f"{digest}.json").write_bytes(body(MODEL).replace(b"markings", b"markingX"))
        with self.assertRaisesRegex(ArtifactError, "failed digest verification"):
            self.store.read(presentation_digest)
        with self.assertRaisesRegex(ArtifactError, "failed digest verification"):
            self.store.publish(MODEL, "run")

    def test_outputs_are_published_under_their_declaration_and_read_by_reference(self) -> None:
        model = self.store.publish(MODEL, "earlier")
        bound = {
            "version": 1,
            "kind": "graded-presentation",
            "payload": {"model_digest": model, "source": [], "target": [], "matrix": []},
        }
        declared = {"surface": "k3-model", "sheaf": "graded-presentation"}
        references = self.store.publish_outputs({"surface": MODEL, "sheaf": bound}, declared, "attempt")
        self.assertEqual(references["surface"], {"kind": "k3-model", "digest": model})
        self.assertEqual(references["sheaf"]["kind"], "graded-presentation")
        for staged, problem in (
            ({"surface": MODEL}, "names must match"),
            ({"surface": MODEL, "sheaf": bound, "extra": MODEL}, "names must match"),
            ([MODEL, bound], "names must match"),
            ({"surface": bound, "sheaf": bound}, "output surface must be a k3-model artifact"),
            ({"surface": MODEL, "sheaf": "text"}, "output sheaf must be a graded-presentation artifact"),
        ):
            with self.subTest(problem=problem), self.assertRaisesRegex(ArtifactError, problem):
                self.store.publish_outputs(staged, declared, "attempt")

        read = self.store.output(references["sheaf"], "sheaf", "graded-presentation")
        self.assertEqual(read, {"digest": references["sheaf"]["digest"], "data": bound})
        self.assertEqual((model_digest(read["data"]), model_digest(MODEL)), (model, None))
        for reference, kind, problem in (
            (None, "k3-model", "missing k3-model artifact surface"),
            (references["sheaf"], "k3-model", "missing k3-model artifact surface"),
            ({"kind": "k3-model"}, "k3-model", "missing digest for artifact surface"),
            (
                {"kind": "k3-model", "digest": references["sheaf"]["digest"]},
                "k3-model",
                "has kind graded-pres",
            ),
            ({"kind": "k3-model", "digest": "0" * 64}, "k3-model", "is not registered"),
        ):
            with self.subTest(problem=problem), self.assertRaisesRegex(ArtifactError, problem):
                self.store.output(reference, "surface", kind)

    def test_chain_map_requires_verified_complex_endpoints_over_the_same_model(self) -> None:
        model = self.store.publish(MODEL, "model")
        other = self.store.publish(MODEL | {"payload": MODEL["payload"] | {"coordinates": ["x"]}}, "model")
        complex_data = {
            "version": 1,
            "kind": "graded-complex",
            "payload": {"model_digest": model, "base": 0, "terms": [[0]], "differentials": []},
        }
        source = self.store.publish(complex_data, "source")
        target = self.store.publish(
            complex_data | {"payload": complex_data["payload"] | {"base": 1}}, "target"
        )
        wrong_model = self.store.publish(
            complex_data | {"payload": complex_data["payload"] | {"model_digest": other}}, "target"
        )
        info = {"model_digest": model, "source_digest": source, "target_digest": target, "components": []}
        chain_map = {"version": 1, "kind": "graded-chain-map", "payload": info}
        digest = self.store.publish(chain_map, "map")
        self.assertEqual(self.store.read(digest), body(chain_map))
        for bad, message in [
            ("", "expected a lowercase SHA-256 digest"),
            ("f" * 64, "not registered"),
            (model, "must name a graded complex"),
            (wrong_model, "must name a graded complex"),
        ]:
            with self.subTest(endpoint=bad), self.assertRaisesRegex(ArtifactError, message):
                self.store.publish(chain_map | {"payload": info | {"target_digest": bad}}, "invalid")
        staged = chain_map | {
            "payload": {
                "model_digest": model,
                "source_output": "src",
                "target_output": "dst",
                "components": [],
            }
        }
        declared = {"arrow": "graded-chain-map", "src": "graded-complex", "dst": "graded-complex"}
        outputs = {
            "arrow": staged,
            "src": complex_data,
            "dst": complex_data | {"payload": complex_data["payload"] | {"base": 1}},
        }
        self.assertEqual(self.store.publish_outputs(outputs, declared, "staged")["arrow"]["digest"], digest)
        wrong = staged | {"payload": staged["payload"] | {"target_output": "arrow"}}
        with self.assertRaisesRegex(ArtifactError, "must name a graded-complex sibling output"):
            self.store.publish_outputs(outputs | {"arrow": wrong}, declared, "invalid")
        (self.store.objects / f"{source}.json").write_bytes(b"damaged")
        with self.assertRaisesRegex(ArtifactError, "failed digest verification"):
            self.store.read(digest)

    def test_cli_publishes_and_reads_canonical_bytes(self) -> None:
        directory = self.store.database.parent
        raw = directory / "model.json"
        raw.write_text(json.dumps(MODEL, indent=2), encoding="utf-8")

        def invoke(*args: str) -> bytes:
            return subprocess.check_output([sys.executable, "-m", "batch", *args], timeout=15)

        digest = invoke("publish-artifact", str(directory), str(raw), "--producer", "run-1").decode().strip()
        self.assertEqual(invoke("read-artifact", str(directory), digest), body(MODEL))

    def test_version_two_is_specific_to_complexes(self) -> None:
        model = self.store.publish(MODEL, "model")
        presentation = {
            "version": 2,
            "kind": "graded-presentation",
            "payload": {"model_digest": model, "source": [], "target": [], "matrix": []},
        }
        with self.assertRaisesRegex(ArtifactError, "unknown artifact version"):
            self.store.publish(MODEL | {"version": 2}, "model")
        with self.assertRaisesRegex(ArtifactError, "unknown artifact version"):
            self.store.publish(presentation, "presentation")


@unittest.skipUnless(shutil.which("M2"), "Macaulay2 is not installed")
class Macaulay2ArtifactRoundTrip(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.store = ArtifactStore(self.directory / "store")

    def run_m2(self, name: str, code: str) -> None:
        script = self.directory / f"{name}.m2"
        script.write_text(
            'path = prepend("./src/macaulay2/", path); needsPackage "K3Twists"; needsPackage "JSON"; '
            'needsPackage "Complexes";\n'
            f"outDir = {json.dumps(str(self.directory) + '/')};\n"
            'emitData = (name, D) -> (outDir | name | ".json") << toJSON D << close;\n'
            'readData = name -> fromJSON get(outDir | name | ".json");\n' + code,
            encoding="utf-8",
        )
        finished = subprocess.run(["M2", "--script", str(script)], capture_output=True, text=True, timeout=40)
        self.assertEqual(finished.returncode, 0, finished.stdout + finished.stderr)

    def register(self, name: str) -> str:
        data = read_artifact_json((self.directory / f"raw-{name}.json").read_bytes())
        digest = self.store.publish(data, f"compute-{name}")
        (self.directory / f"{name}.json").write_bytes(self.store.read(digest))
        return digest

    def test_marked_model_kernel_bundle_and_cones(self) -> None:
        self.run_m2(
            "write-model",
            """
            K = realizeK3Surface k3Recipe hashTable {"family" => "quartic_with_conic"};
            emitData("raw-model", k3ModelArtifact K);
            """,
        )

        model = self.register("model")
        self.run_m2(
            "write-presentation-and-complex",
            f"""
            portable = readData "model";
            K = realizeK3Surface k3Recipe hashTable {{"family" => "quartic_with_conic"}};
            bindK3ModelArtifact(K, portable, "{model}");
            assert(divisorPairing(K#"polarization", markedCurveClass K) === 2);
            assert(k3ModelArtifact K === readData "model");
            R = K#"ring";
            emitData("raw-presentation", gradedPresentationArtifact(K, module kernelBundle K, "{model}"));
            C = complex({{map(R^{{1}}, R^4, vars R)}}, Base => -2);
            emitData("raw-complex", gradedComplexArtifact(K, C, "{model}"));
            E = complex {{map(R^1, R^1, 1), map(R^1, R^1, 0)}};
            emitData("raw-three-term", gradedComplexArtifact(K, E, "{model}"));
            W = twistWord {{twistStep(sphericalObject structureObject K, 1)}};
            P = realizeTwistImage applyWord(W, catalogueObject(K, "O_x"));
            assert(P#"status" === "realized");
            assert(not isFreeModule (P#"complex")_0);
            emitData("raw-point-cone", gradedComplexArtifact(K, P#"complex", "{model}"));
            """,
        )
        self.register("presentation")
        self.register("complex")
        self.register("three-term")
        self.register("point-cone")
        self.run_m2(
            "reload",
            f"""
            K = loadK3ModelArtifact(readData "model", "{model}");
            P = readData "presentation";
            F = sheaf loadGradedPresentation(K, P);
            assert({{rank F, cohomologyDims F}} === {{3,{{0,0,4}}}});
            Q = readData "complex";
            assert(Q#"version" === 1 and Q#"payload"#"terms" === {{{{-1}},{{0,0,0,0}}}});
            C = loadGradedComplex(K, Q);
            assert(concentration C === (-2,-1));
            assert(HH_(-2) C != 0 and sheaf HH_(-2) C == 0);
            assert(cohomologyDims sheaf HH_(-1) C === {{0,0,4}});
            R = K#"ring";
            assert(sheaf HH_(-1) C == kernelBundle K);
            assert(gradedComplexArtifact(K, C, "{model}") === Q);
            other = loadK3ModelArtifact(readData "model", concatenate toList(64:"f"));
            assert(try (loadGradedPresentation(other, P); false) else true);
            assert(try (gradedPresentationArtifact(other, module F, "{model}"); false) else true);
            editPayload = (envelope, key, item) -> merge(envelope, hashTable {{
                "payload" => merge(envelope#"payload", hashTable {{key => item}}, (a,b) -> b)
                }}, (a,b) -> b);
            assert(try (loadGradedComplex(K, editPayload(Q, "differentials", {{}})); false) else true);
            wrongShifts = {{{{0}},{{0,0,0,0}}}};
            assert(try (loadGradedComplex(K, editPayload(Q, "terms", wrongShifts)); false) else true);
            T = readData "three-term";
            assert(isWellDefined loadGradedComplex(K, T));
            nonzero = first select(T#"payload"#"differentials", a -> a#0#0 =!= {{}});
            assert(try (loadGradedComplex(K, editPayload(T, "differentials", {{nonzero,nonzero}})); false)
                else true);

            pointData = readData "point-cone";
            assert(pointData#"version" === 2);
            pointCone = loadGradedComplex(K, pointData);
            assert(concentration pointCone === (0,1) and isWellDefined pointCone);
            assert(degrees pointCone_0 === {{{{0}}}} and degrees pointCone_1 === {{{{0}}}});
            assert(pointCone_0 == module pointSheaf K and isFreeModule pointCone_1);
            assert(degree (pointCone.dd)_1 === {{0}} and ((pointCone.dd)_1)_(0,0) == 1_R);
            shiftedIdeal = complex(module pointIdealSheaf K, Base => 1);
            assert(HH_1 pointCone == HH_1 shiftedIdeal and HH_0 pointCone == 0);
            assert(sheaf HH_1 pointCone == pointIdealSheaf K and sheaf HH_0 pointCone == 0);
            assert(cohomologyDims sheaf HH_1 pointCone === {{0,0,1}});
            assert(gradedComplexArtifact(K, pointCone, "{model}") === pointData);
            assert(try (loadGradedComplex(other, pointData); false) else true);

            x0 = (vars R)_(0,0);
            x1 = (vars R)_(0,1);
            A = coker map(R^1, R^{{-1}}, {{{{x1}}}});
            B = coker map(R^1, R^{{-2}}, {{{{x0*x1}}}});
            ontoA = map(A, B, {{{{1_R}}}});
            intoB = map(B, R^{{-1}}, {{{{x1}}}});
            E = complex({{ontoA, intoB}}, Base => -1);
            data = gradedComplexArtifact(K, E, "{model}");
            loaded = loadGradedComplex(K, data);
            assert(concentration loaded === (-1,1) and isWellDefined loaded);
            -- The lifts compose to x1. The composition is zero in the target quotient.
            assert(matrix ((loaded.dd)_0) * matrix ((loaded.dd)_1) != 0);
            diffs = data#"payload"#"differentials";
            linear = {{{{{{1,0,0,0}}, 1}}}};
            linearMap = {{{{linear}}}};
            badDegree = editPayload(data, "differentials", {{linearMap, last diffs}});
            badSquare = editPayload(data, "differentials", {{first diffs, linearMap}});
            termData = data#"payload"#"terms";
            x0Term = hashTable {{"source" => {{1}}, "target" => {{0}}, "matrix" => linearMap}};
            badDescent = editPayload(data, "terms", {{first termData, x0Term, last termData}});
            scan({{badDegree, badSquare, badDescent}}, bad ->
                assert(try (loadGradedComplex(K, bad); false) else true));
            """,
        )

    def test_quartic_evaluation_and_augmentation_round_trip(self) -> None:
        self.run_m2(
            "write-quartic",
            """
            K = realizeK3Surface k3Recipe hashTable {"family" => "quartic_with_line"};
            emitData("raw-model", k3ModelArtifact K);
            """,
        )
        model = self.register("model")
        self.run_m2(
            "write-endpoints",
            f"""
            K = loadK3ModelArtifact(readData "model", "{model}");
            W = twistWord {{twistStep(sphericalObject structureObject K, 1)}};
            F = realizeTwistImage(W, catalogueObject(K, "O(-1H)"));
            u = F#"chainMap";
            a = F#"sourceAugmentation";
            assert(source u == source a);
            emitData("raw-source", gradedComplexArtifact(K, source u, "{model}"));
            emitData("raw-line", gradedComplexArtifact(K, target u, "{model}"));
            emitData("raw-structure", gradedComplexArtifact(K, target a, "{model}"));
            """,
        )
        src, line, structure = (self.register(name) for name in ("source", "line", "structure"))
        self.run_m2(
            "write-maps",
            f"""
            K = loadK3ModelArtifact(readData "model", "{model}");
            W = twistWord {{twistStep(sphericalObject structureObject K, 1)}};
            F = realizeTwistImage(W, catalogueObject(K, "O(-1H)"));
            emitData("raw-evaluation", gradedChainMapArtifact(K, F#"chainMap",
                "{model}", ("{src}", "{line}")));
            emitData("raw-augmentation", gradedChainMapArtifact(K, F#"sourceAugmentation",
                "{model}", ("{src}", "{structure}")));
            """,
        )
        self.register("evaluation")
        self.register("augmentation")
        self.run_m2(
            "reload-maps",
            f"""
            K = loadK3ModelArtifact(readData "model", "{model}");
            D = loadGradedComplex(K, readData "source");
            L = loadGradedComplex(K, readData "line");
            O = loadGradedComplex(K, readData "structure");
            U = readData "evaluation";
            A = readData "augmentation";
            u = loadGradedChainMap(K, U, (D, "{src}"), (L, "{line}"));
            a = loadGradedChainMap(K, A, (D, "{src}"), (O, "{structure}"));
            assert(source u === D and source a === D);
            assert(target u === L and target a === O);
            assert(all({{u,a}}, f -> isComplexMorphism f and isWellDefined f and isHomogeneous f));
            assert(gradedChainMapArtifact(K, u, "{model}", ("{src}", "{line}")) === U);
            assert(gradedChainMapArtifact(K, a, "{model}", ("{src}", "{structure}")) === A);
            assert(concentration O === (-2,-2));
            assert(isIsomorphism sheaf homology(-2, a));
            assert(all({{-1,0}}, i -> sheaf HH_i D == 0));
            C = cone u;
            assert(isIsomorphism sheaf homology(0, canonicalMap(C, L)));
            assert(isIsomorphism sheaf homology(-1, a[-1] * canonicalMap(D[-1], C)));
            assert(try (loadGradedChainMap(K, U, (D, "{src}"), (O, "{structure}")); false) else true);
            assert(try (loadGradedChainMap(K, U, (D, "{line}"), (L, "{line}")); false) else true);
            editPayload = (envelope, key, item) -> merge(envelope, hashTable {{
                "payload" => merge(envelope#"payload", hashTable {{key => item}}, (a,b) -> b)
                }}, (a,b) -> b);
            assert(try (loadGradedChainMap(K, editPayload(U, "components", {{}}),
                (D, "{src}"), (L, "{line}")); false) else true);
            assert(try (loadGradedChainMap(K, editPayload(U, "model_digest", "{line}"),
                (D, "{src}"), (L, "{line}")); false) else true);

            R = K#"ring";
            P = complex module pointSheaf K;
            G = complex R^1;
            pointMap = map(P, G, hashTable {{0 => map(P_0, G_0, 1)}});
            P = loadGradedComplex(K, gradedComplexArtifact(K, P, "{model}"));
            assert(not isFreeModule P_0);
            Q = gradedChainMapArtifact(K, pointMap, "{model}", ("{line}", "{structure}"));
            q = loadGradedChainMap(K, Q, (G, "{line}"), (P, "{structure}"));
            assert(isWellDefined q_0 and isComplexMorphism q and q_0_(0,0) == 1_R);
            backwards = editPayload(editPayload(Q, "source_digest", "{structure}"),
                "target_digest", "{line}");
            assert(try (loadGradedChainMap(K, backwards, (P, "{structure}"), (G, "{line}")); false)
                else true);

            F = complex {{id_(R^1)}};
            I = gradedChainMapArtifact(K, map(F, F, 1), "{model}", ("{line}", "{line}"));
            matrices = I#"payload"#"components";
            broken = editPayload(I, "components", {{{{{{{{}}}}}}, matrices#1}});
            assert(try (loadGradedChainMap(K, broken, (F, "{line}"), (F, "{line}")); false) else true);
            """,
        )
