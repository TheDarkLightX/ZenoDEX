from __future__ import annotations

from pathlib import Path

from tools.check_release_publication_workflow import (
    DEFAULT_WORKFLOW,
    check_release_publication_workflow,
    main,
)


def test_release_publication_workflow_passes_current_file() -> None:
    report = check_release_publication_workflow(DEFAULT_WORKFLOW)

    assert report["schema"] == "zenodex.release_publication_workflow_check.v0"
    assert report["ok"] is True


def test_release_publication_workflow_rejects_missing_github_release(
    tmp_path: Path,
) -> None:
    workflow = tmp_path / "release-publish.yml"
    text = DEFAULT_WORKFLOW.read_text(encoding="utf-8").replace(
        "softprops/action-gh-release@v2",
        "missing-release-action",
    )
    workflow.write_text(text, encoding="utf-8")

    report = check_release_publication_workflow(workflow)

    assert report["ok"] is False
    assert (
        "release publication workflow must contain softprops/action-gh-release@v2"
        in report["errors"]
    )


def test_release_publication_workflow_rejects_top_level_write(tmp_path: Path) -> None:
    workflow = tmp_path / "release-publish.yml"
    text = DEFAULT_WORKFLOW.read_text(encoding="utf-8").replace(
        "permissions:\n  contents: read",
        "permissions:\n  contents: write",
        1,
    )
    workflow.write_text(text, encoding="utf-8")

    report = check_release_publication_workflow(workflow)

    assert report["ok"] is False
    assert (
        "release publication workflow must keep top-level permissions at contents: read"
        in report["errors"]
    )


def test_release_publication_workflow_rejects_automatic_npm_publish(
    tmp_path: Path,
) -> None:
    workflow = tmp_path / "release-publish.yml"
    text = DEFAULT_WORKFLOW.read_text(encoding="utf-8").replace(
        "if: ${{ github.event_name == 'workflow_dispatch' && inputs.publish_npm }}",
        "if: ${{ github.event_name == 'push' || inputs.publish_npm }}",
    )
    workflow.write_text(text, encoding="utf-8")

    report = check_release_publication_workflow(workflow)

    assert report["ok"] is False
    assert "npm publish must remain manual opt-in" in report["errors"]


def test_release_publication_workflow_rejects_manual_only_container_publish(
    tmp_path: Path,
) -> None:
    workflow = tmp_path / "release-publish.yml"
    text = DEFAULT_WORKFLOW.read_text(encoding="utf-8").replace(
        "if: ${{ github.event_name == 'push' || inputs.publish_containers }}",
        "if: ${{ github.event_name == 'workflow_dispatch' && inputs.publish_containers }}",
    )
    workflow.write_text(text, encoding="utf-8")

    report = check_release_publication_workflow(workflow)

    assert report["ok"] is False
    assert (
        "container publish must run on tag pushes or manual opt-in" in report["errors"]
    )


def test_release_publication_workflow_rejects_manual_publish_defaults_true(
    tmp_path: Path,
) -> None:
    workflow = tmp_path / "release-publish.yml"
    text = DEFAULT_WORKFLOW.read_text(encoding="utf-8").replace(
        "publish_github_release:\n"
        '        description: "Create or update a GitHub Release and attach artifacts."\n'
        "        required: true\n"
        "        default: false",
        "publish_github_release:\n"
        '        description: "Create or update a GitHub Release and attach artifacts."\n'
        "        required: true\n"
        "        default: true",
    )
    workflow.write_text(text, encoding="utf-8")

    report = check_release_publication_workflow(workflow)

    assert report["ok"] is False
    assert (
        "manual workflow_dispatch input publish_github_release must default to false"
        in report["errors"]
    )


def test_release_publication_workflow_rejects_npm_token_during_prepare(
    tmp_path: Path,
) -> None:
    workflow = tmp_path / "release-publish.yml"
    text = DEFAULT_WORKFLOW.read_text(encoding="utf-8").replace(
        "      - name: Prepare package\n" "        run: |",
        "      - name: Prepare package\n"
        "        env:\n"
        "          NODE_AUTH_TOKEN: ${{ secrets.NPM_TOKEN }}\n"
        "        run: |",
    )
    workflow.write_text(text, encoding="utf-8")

    report = check_release_publication_workflow(workflow)

    assert report["ok"] is False
    assert (
        "NPM_TOKEN must only be exposed to the minimal npm publish step"
        in report["errors"]
    )


def test_release_publication_workflow_rejects_npm_token_at_job_scope(
    tmp_path: Path,
) -> None:
    workflow = tmp_path / "release-publish.yml"
    text = DEFAULT_WORKFLOW.read_text(encoding="utf-8").replace(
        "  publish-npm:\n    name: Publish npm SDK",
        "  publish-npm:\n"
        "    env:\n"
        "      NODE_AUTH_TOKEN: ${{ secrets.NPM_TOKEN }}\n"
        "    name: Publish npm SDK",
    )
    workflow.write_text(text, encoding="utf-8")

    report = check_release_publication_workflow(workflow)

    assert report["ok"] is False
    assert (
        "NPM_TOKEN must only be exposed to the minimal npm publish step"
        in report["errors"]
    )


def test_release_publication_workflow_rejects_npm_token_in_extra_step(
    tmp_path: Path,
) -> None:
    workflow = tmp_path / "release-publish.yml"
    text = DEFAULT_WORKFLOW.read_text(encoding="utf-8").replace(
        "      - name: Prepare package",
        "      - name: Leaky preflight\n"
        "        env:\n"
        "          NODE_AUTH_TOKEN: ${{ secrets.NPM_TOKEN }}\n"
        "        run: npm whoami\n\n"
        "      - name: Prepare package",
    )
    workflow.write_text(text, encoding="utf-8")

    report = check_release_publication_workflow(workflow)

    assert report["ok"] is False
    assert (
        "NPM_TOKEN must only be exposed to the minimal npm publish step"
        in report["errors"]
    )


def test_release_publication_workflow_does_not_borrow_sibling_job_permissions(
    tmp_path: Path,
) -> None:
    workflow = tmp_path / "release-publish.yml"
    text = DEFAULT_WORKFLOW.read_text(encoding="utf-8").replace(
        "      packages: write\n      id-token: write",
        "      packages: write",
        1,
    )
    workflow.write_text(text, encoding="utf-8")

    report = check_release_publication_workflow(workflow)

    assert report["ok"] is False
    assert (
        "release publication workflow job permission check failed: "
        "publish_containers_packages_write"
        in report["errors"]
    )


def test_release_publication_workflow_rejects_publish_lifecycle_scripts(
    tmp_path: Path,
) -> None:
    workflow = tmp_path / "release-publish.yml"
    text = DEFAULT_WORKFLOW.read_text(encoding="utf-8").replace(
        "npm publish --access public --provenance --ignore-scripts *.tgz",
        "npm publish --access public --provenance *.tgz",
    )
    workflow.write_text(text, encoding="utf-8")

    report = check_release_publication_workflow(workflow)

    assert report["ok"] is False
    assert (
        "NPM_TOKEN must only be exposed to the minimal npm publish step"
        in report["errors"]
    )


def test_release_publication_workflow_cli_outputs_json(capsys) -> None:  # type: ignore[no-untyped-def]
    code = main(["--workflow", str(DEFAULT_WORKFLOW)])
    out = capsys.readouterr().out

    assert code == 0
    assert "zenodex.release_publication_workflow_check.v0" in out
