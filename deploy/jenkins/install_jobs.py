"""Install the repository-managed Goldbach Jenkins pipelines."""

import argparse
import xml.etree.ElementTree as ET
from pathlib import Path
from urllib.error import HTTPError

from jenkins_client import Jenkins

JOBS = {
    "goldbach-isolated-proof": ("proof-isolated", "Lean proof advisory"),
    "goldbach-formal-isolated": ("formal-isolated", "Formal Lean proof verification"),
    "goldbach-isolated-catalogue": ("catalogue-isolated", "Goldbach catalogue verification"),
    "goldbach-isolated-grh": ("grh-isolated", "GRH full-source verification"),
    "goldbach-isolated-site": ("site-isolated", "Website PR verification"),
    "goldbach-site-revision": ("site-revision", "Website release verification"),
}
PARAMETERS = ("CI_JOB_ID", "CI_HEAD", "CI_PR", "CI_TRIGGER")
PARAMETER_PATH = "properties/hudson.model.ParametersDefinitionProperty/parameterDefinitions"


def configuration(script, description, *, disabled=False):
    job = ET.Element("flow-definition")
    ET.SubElement(job, "description").text = description
    properties = ET.SubElement(job, "properties")
    property_node = ET.SubElement(properties, "hudson.model.ParametersDefinitionProperty")
    parameters = ET.SubElement(property_node, "parameterDefinitions")
    for name in PARAMETERS:
        parameter = ET.SubElement(parameters, "hudson.model.StringParameterDefinition")
        ET.SubElement(parameter, "name").text = name
        ET.SubElement(parameter, "defaultValue")
        ET.SubElement(parameter, "trim").text = "false"
    definition = ET.SubElement(job, "definition", {"class": "org.jenkinsci.plugins.workflow.cps.CpsFlowDefinition"})
    ET.SubElement(definition, "script").text = script
    ET.SubElement(definition, "sandbox").text = "true"
    ET.SubElement(job, "disabled").text = "true" if disabled else "false"
    return job


def managed_settings(job):
    definition = job.find("definition")
    parameters = [
        (param.tag, param.findtext("name"), param.findtext("defaultValue", ""), param.findtext("trim", "false"))
        for param in job.findall(PARAMETER_PATH + "/*")
    ]
    return (job.findtext("description"), job.findtext("disabled"), definition.get("class"),
            definition.findtext("script"), definition.findtext("sandbox"), parameters)


def install(client, folder, *, job=None, grh_enabled=False):
    for name in (job,) if job else JOBS:
        file, description = JOBS[name]
        config = configuration(
            (folder / ("Jenkinsfile." + file)).read_text(encoding="utf-8"),
            description,
            disabled=name == "goldbach-isolated-grh" and not grh_enabled,
        )
        path = client.job_path(name) + "/config.xml"
        try:
            with client.request(path) as response:
                current = ET.fromstring(response.read())
        except HTTPError as error:
            if error.code != 404:
                raise
            endpoint, action = "/createItem?name=" + name, "created"
        else:
            if managed_settings(current) == managed_settings(config):
                print(f"{name} verified")
                continue
            endpoint, action = path, "updated"
        with client.request(endpoint, ET.tostring(config, encoding="utf-8"), content_type="application/xml"):
            pass
        with client.request(path) as response:
            installed = ET.fromstring(response.read())
        if managed_settings(installed) != managed_settings(config):
            raise RuntimeError(f"Jenkins did not retain the expected configuration for {name}")
        print(f"{name} {action} and verified")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--url", required=True)
    parser.add_argument("--user", required=True)
    parser.add_argument("--credential", type=Path, required=True)
    parser.add_argument("--job", choices=JOBS)
    parser.add_argument("--enable-grh", action="store_true")
    args = parser.parse_args()
    client = Jenkins(args.url, args.user, args.credential.read_text().strip())
    install(client, Path(__file__).resolve().parent, job=args.job, grh_enabled=args.enable_grh)


if __name__ == "__main__":
    main()
