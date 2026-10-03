#!/usr/bin/env python3
"""
Build a publication-record PDF from a public ORCID record.

Usage:
    python orcid_publications.py
    python orcid_publications.py --orcid 0000-0001-7529-9834
    python orcid_publications.py --jcr jcr_metrics.csv

Outputs:
    publication_record.tex
    publication_record.pdf
    jcr_needed_issns.csv
"""

import argparse
import csv
import re
import unicodedata
import shutil
import subprocess
import sys
import time
from collections import Counter
from datetime import date
from pathlib import Path

import requests


DEFAULT_ORCID = "0000-0001-7529-9834"
ORCID_API = "https://pub.orcid.org/v3.0"


def get_json(url, headers=None, timeout=30):
    r = requests.get(url, headers=headers or {}, timeout=timeout)
    r.raise_for_status()
    return r.json()


def clean_text(value):
    """Clean ORCID metadata before passing it to LaTeX."""
    text = str(value or "")

    # Normalize common HTML markup found in publication titles.
    text = re.sub(
        r"<\s*SUP\s*>(.*?)<\s*/\s*SUP\s*>",
        r"^\\1",
        text,
        flags=re.I,
    )
    text = re.sub(
        r"<\s*SUB\s*>(.*?)<\s*/\s*SUB\s*>",
        r"_\\1",
        text,
        flags=re.I,
    )
    text = re.sub(r"<[^>]+>", "", text)

    # Remove malformed Unicode/encoding artifacts occasionally present in
    # author metadata, e.g. Br^?auninger -> Brauninger.
    text = text.replace("^?", "")
    text = text.replace("\ufffd", "")

    text = re.sub(r"\s+", " ", text).strip()
    return text


def latex_escape(text):
    """Escape text for LaTeX while preserving our generated LaTeX snippets
    and converting simple math markup commonly found in publication metadata
    into safe LaTeX.
    """
    if text is None:
        return ""

    text = str(text)

    # Convert common inline math constructs found in publication metadata.
    # Example: "$^{37}$Ar" -> "\textsuperscript{37}Ar"
    text = re.sub(
        r'\$\^\{([^{}]+)\}\$',
        lambda m: r'\textsuperscript{' + m.group(1) + '}',
        text
    )
    text = re.sub(
        r'\$\_\{([^{}]+)\}\$',
        lambda m: r'\textsubscript{' + m.group(1) + '}',
        text
    )

    # Protect any remaining generated LaTeX commands/snippets.
    placeholders = []

    def protect(match):
        placeholders.append(match.group(0))
        return f"@@LATEX{len(placeholders)-1}@@"

    # Protect commands with braced arguments, commands without arguments,
    # and common math snippets.
    text = re.sub(
        r'\\(?:textsuperscript|textsubscript|textit|textbf|emph|'
        r'textquotesingle|textasciicircum|textasciitilde)\{[^{}]*\}'
        r'|\\[A-Za-z@]+',
        protect,
        text
    )

    # Latin Unicode characters are converted to LaTeX accents.  This keeps
    # the generated .tex ASCII-safe even when publication metadata contains
    # names such as Bräuninger, García, Müller, etc.
    latin_map = {
        "ä": r'\"{a}', "Ä": r'\"{A}', "ö": r'\"{o}', "Ö": r'\"{O}',
        "ü": r'\"{u}', "Ü": r'\"{U}', "ë": r'\"{e}', "Ë": r'\"{E}',
        "ï": r'\"{i}', "Ï": r'\"{I}', "ÿ": r'\"{y}',
        "á": r"\'{a}", "Á": r"\'{A}", "é": r"\'{e}", "É": r"\'{E}",
        "í": r"\'{i}", "Í": r"\'{I}", "ó": r"\'{o}", "Ó": r"\'{O}",
        "ú": r"\'{u}", "Ú": r"\'{U}", "ý": r"\'{y}", "Ý": r"\'{Y}",
        "à": r'\`{a}', "À": r'\`{A}', "è": r'\`{e}', "È": r'\`{E}',
        "ì": r'\`{i}', "Ì": r'\`{I}', "ò": r'\`{o}', "Ò": r'\`{O}',
        "ù": r'\`{u}', "Ù": r'\`{U}',
        "â": r'\^{a}', "Â": r'\^{A}', "ê": r'\^{e}', "Ê": r'\^{E}',
        "î": r'\^{i}', "Î": r'\^{I}', "ô": r'\^{o}', "Ô": r'\^{O}',
        "û": r'\^{u}', "Û": r'\^{U}',
        "ã": r'\~{a}', "Ã": r'\~{A}', "ñ": r'\~{n}', "Ñ": r'\~{N}',
        "õ": r'\~{o}', "Õ": r'\~{O}',
        "å": r'\AA{}', "Å": r'\AA{}', "æ": r'\ae{}', "Æ": r'\AE{}',
        "ø": r'\o{}', "Ø": r'\O{}', "ç": r'\c{c}', "Ç": r'\c{C}',
        "š": r'\v{s}', "Š": r'\v{S}', "č": r'\v{c}', "Č": r'\v{C}',
        "ž": r'\v{z}', "Ž": r'\v{Z}', "ř": r'\v{r}', "Ř": r'\v{R}',
        "ě": r'\v{e}', "Ě": r'\v{E}', "ů": r'\r{u}', "Ů": r'\r{U}',
        "ł": r'\l{}', "Ł": r'\L{}', "ń": r"\'{n}", "Ń": r"\'{N}",
        "ś": r"\'{s}", "Ś": r"\'{S}", "ź": r"\'{z}", "Ź": r"\'{Z}",
        "ż": r'\.{z}', "Ż": r'\.{Z}', "ą": r'\k{a}', "Ą": r'\k{A}',
        "ę": r'\k{e}', "Ę": r'\k{E}', "ğ": r'\u{g}', "Ğ": r'\u{G}',
        "ş": r'\c{s}', "Ş": r'\c{S}', "ı": r'{\i}',
        "İ": r'\.{I}', "ð": r'\dh{}', "Ð": r'\DH{}',
        "þ": r'\th{}', "Þ": r'\TH{}', "ß": r'\ss{}',
    }
    for old, new in latin_map.items():
        text = text.replace(old, new)

    # Common Unicode characters found in publication metadata.
    # These are converted to LaTeX before the ordinary escaping stage.
    unicode_map = {
        "α": r"$\alpha$",
        "β": r"$\beta$",
        "γ": r"$\gamma$",
        "δ": r"$\delta$",
        "ε": r"$\epsilon$",
        "ϵ": r"$\epsilon$",
        "ζ": r"$\zeta$",
        "η": r"$\eta$",
        "θ": r"$\theta$",
        "ϑ": r"$\vartheta$",
        "ι": r"$\iota$",
        "κ": r"$\kappa$",
        "λ": r"$\lambda$",
        "μ": r"$\mu$",
        "ν": r"$\nu$",
        "ξ": r"$\xi$",
        "π": r"$\pi$",
        "ρ": r"$\rho$",
        "σ": r"$\sigma$",
        "τ": r"$\tau$",
        "υ": r"$\upsilon$",
        "φ": r"$\phi$",
        "ϕ": r"$\varphi$",
        "χ": r"$\chi$",
        "ψ": r"$\psi$",
        "ω": r"$\omega$",
        "Γ": r"$\Gamma$",
        "Δ": r"$\Delta$",
        "Θ": r"$\Theta$",
        "Λ": r"$\Lambda$",
        "Ξ": r"$\Xi$",
        "Π": r"$\Pi$",
        "Σ": r"$\Sigma$",
        "Υ": r"$\Upsilon$",
        "Φ": r"$\Phi$",
        "Ψ": r"$\Psi$",
        "Ω": r"$\Omega$",
        "±": r"$\\pm$",
        "×": r"$\\times$",
        "≤": r"$\\leq$",
        "≥": r"$\\geq$",
        "→": r"$\\rightarrow$",
        "∞": r"$\\infty$",
    }

    for old, new in unicode_map.items():
        text = text.replace(old, new)

    # Protect the generated math snippets before escaping literal '$'.
    math_placeholders = []

    def protect_math(match):
        math_placeholders.append(match.group(0))
        return f"@@MATH{len(math_placeholders)-1}@@"

    text = re.sub(r'\$[^$]+\$', protect_math, text)

    # Protect generated LaTeX accent commands before escaping their backslashes.
    # This pattern is deliberately simple and avoids Python string-quoting
    # pitfalls with apostrophes and backslashes.
    text = re.sub(
        r'\\(?:v|r|c|k|u|\.|\"|`|\'|~|\^)\{[^{}]*\}'
        r'|\\(?:AA|AE|O|ae|dh|DH|th|TH|ss|l|L|i)\{\}',
        protect,
        text
    )

    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
        "$": r"\$",
    }

    for old, new in replacements.items():
        text = text.replace(old, new)

    for i, snippet in enumerate(placeholders):
        text = text.replace(f"@@LATEX{i}@@", snippet)

    for i, snippet in enumerate(math_placeholders):
        text = text.replace(f"@@MATH{i}@@", snippet)

    return text


def latex_url(value):
    value = clean_text(value)
    return (value.replace("\\", r"\textbackslash{}")
                 .replace("#", r"\#")
                 .replace("%", r"\%")
                 .replace("&", r"\&"))


def get_orcid_works(orcid):
    headers = {
        "Accept": "application/vnd.orcid+json",
        "User-Agent": "orcid-publications-script/1.0",
    }

    summary = get_json(f"{ORCID_API}/{orcid}/works", headers=headers)
    groups = summary.get("group", [])

    works = []
    seen = set()

    for group in groups:
        summaries = group.get("work-summary", [])
        if not summaries:
            continue

        chosen = summaries[0]
        put_code = chosen.get("put-code")
        if put_code is None or put_code in seen:
            continue
        seen.add(put_code)

        try:
            work = get_json(
                f"{ORCID_API}/{orcid}/work/{put_code}",
                headers=headers,
            )
        except Exception as exc:
            print(f"Warning: could not retrieve ORCID work {put_code}: {exc}")
            continue

        works.append(work)

    return works


def extract_year(work):
    pub_date = work.get("publication-date") or {}
    year = (pub_date.get("year") or {}).get("value")
    try:
        return int(year) if year else None
    except (TypeError, ValueError):
        return None


def extract_title(work):
    return clean_text(((work.get("title") or {}).get("title") or {}).get("value"))


def extract_journal(work):
    return clean_text(((work.get("journal-title") or {}).get("value")))


def extract_type(work):
    return clean_text(work.get("type"))


def extract_doi(work):
    for ext in (work.get("external-ids") or {}).get("external-id", []):
        typ = clean_text(ext.get("external-id-type")).lower()
        value = clean_text(ext.get("external-id-value"))
        if typ == "doi" and value:
            value = re.sub(r"^https?://(dx\.)?doi\.org/", "", value, flags=re.I)
            # ORCID metadata can occasionally contain trailing punctuation
            # or LaTeX/bracket characters after the DOI.
            return value.strip().rstrip(".,;:)]}>")

    url = clean_text((work.get("url") or {}).get("value"))
    m = re.search(r"doi\.org/(10\.\d{4,9}/[^\s<>{}]+)", url, flags=re.I)
    return m.group(1).rstrip(".,;:)]}>") if m else ""


def extract_issns(work):
    values = []
    for ext in (work.get("external-ids") or {}).get("external-id", []):
        typ = clean_text(ext.get("external-id-type")).lower()
        if typ in {"issn", "eissn"}:
            value = re.sub(r"[^0-9Xx]", "", clean_text(ext.get("external-id-value")))
            if value:
                values.append(value.upper())
    return sorted(set(values))


def extract_authors(work):
    authors = []
    for contributor in (work.get("contributors") or {}).get("contributor", []):
        credit = contributor.get("credit-name") or {}
        raw_name = credit.get("value")
        name = clean_text(raw_name)

        # DEBUG: inspect the actual value returned by ORCID and the value
        # after clean_text(), especially for the problematic author.
        if "auninger" in str(raw_name).lower() or "auninger" in name.lower():
            print("DEBUG AUTHOR RAW:  ", repr(raw_name))
            print("DEBUG AUTHOR CLEAN: ", repr(name))
            print("DEBUG AUTHOR RAW HEX:",
                  str(raw_name).encode("utf-8", errors="backslashreplace").hex())
            print("DEBUG AUTHOR CLEAN HEX:",
                  name.encode("utf-8", errors="backslashreplace").hex())

        # Remove literal malformed markers if they are present.
        name = name.replace("^?", "")
        name = name.replace("Br^^?auninger", "Brauninger")
        name = name.replace("Braeuninger", "Brauninger")

        if "auninger" in name.lower():
            print("DEBUG AUTHOR FINAL:", repr(name))

        if name:
            authors.append(name)
    return authors


def normalize_work(work):
    return {
        "title": extract_title(work),
        "journal": extract_journal(work),
        "year": extract_year(work),
        "type": extract_type(work),
        "doi": extract_doi(work),
        "issns": extract_issns(work),
        "authors": extract_authors(work),
    }


def openalex_by_doi(doi):
    if not doi:
        return None

    url = "https://api.openalex.org/works/https://doi.org/" + doi
    headers = {"User-Agent": "orcid-publications-script/1.0"}

    try:
        r = requests.get(url, headers=headers, timeout=30)
        if r.status_code == 404:
            return None
        r.raise_for_status()
        return r.json()
    except Exception as exc:
        print(f"Warning: OpenAlex lookup failed for {doi}: {exc}")
        return None


def add_citations(works):
    """Retrieve OpenAlex citation counts robustly.

    Uses a clean DOI identifier, a descriptive User-Agent, throttling and
    exponential backoff for HTTP 429 responses. A failed lookup never stops
    PDF generation; the work simply keeps a zero/blank citation value.
    """
    import time
    import requests

    session = requests.Session()
    session.headers.update({
        "User-Agent": "ORCID-Publication-Record/1.0 (publication-metrics script)"
    })

    for idx, work in enumerate(works):
        doi = (work.get("doi") or "").strip()

        # Normalize DOI to the bare DOI expected by the OpenAlex API.
        doi = re.sub(r"^https?://doi\.org/", "", doi, flags=re.I)
        doi = re.sub(r"^doi:\s*", "", doi, flags=re.I).strip()

        work["citations"] = 0

        if not doi:
            continue

        # OpenAlex accepts /works/https://doi.org/<DOI>, but the bare DOI
        # form is cleaner and avoids accidental double-prefixing.
        url = "https://api.openalex.org/works/https://doi.org/" + doi

        success = False
        for attempt in range(4):
            try:
                response = session.get(url, timeout=20)

                if response.status_code == 429:
                    retry_after = response.headers.get("Retry-After")
                    if retry_after:
                        try:
                            wait = float(retry_after)
                        except ValueError:
                            wait = 2 ** attempt
                    else:
                        wait = 2 ** attempt

                    print(
                        f"OpenAlex rate limit for {doi}; "
                        f"waiting {wait:.1f}s before retry {attempt + 1}/4..."
                    )
                    time.sleep(wait)
                    continue

                response.raise_for_status()
                data = response.json()
                work["citations"] = int(data.get("cited_by_count", 0) or 0)
                success = True
                break

            except requests.RequestException as exc:
                if attempt < 3:
                    wait = 2 ** attempt
                    print(
                        f"Warning: OpenAlex lookup failed for {doi}: {exc}. "
                        f"Retrying in {wait}s..."
                    )
                    time.sleep(wait)
                else:
                    print(
                        f"Warning: OpenAlex lookup failed for {doi}: {exc}. "
                        "Continuing without citation data."
                    )

        # Gentle throttling even after successful requests.
        if idx < len(works) - 1:
            time.sleep(0.5)

    return works


def normalize_header(header):
    return re.sub(r"[^a-z0-9]+", "", clean_text(header).lower())


def read_jcr(path):
    """
    Accepts either:
      issn,jif,jci,quartile,percentile

    or common Clarivate/JCR CSV exports.
    """
    path = Path(path)
    with path.open("r", encoding="utf-8-sig", newline="") as f:
        rows = list(csv.DictReader(f))

    if not rows:
        return {}

    headers = list(rows[0].keys())
    normalized = {normalize_header(h): h for h in headers}

    def find_header(*names):
        for name in names:
            key = normalize_header(name)
            if key in normalized:
                return normalized[key]
        return None

    issn_h = find_header("issn")
    eissn_h = find_header("eissn")
    jif_h = find_header("jif", "2025 jif", "2024 jif", "journal impact factor")
    jci_h = find_header("jci", "2025 jci", "2024 jci", "journal citation indicator")
    quartile_h = find_header("quartile", "jif quartile", "2025 jif quartile")
    percentile_h = find_header("percentile", "jif percentile", "2025 jif percentile")

    metrics = {}

    for row in rows:
        identifiers = []
        for h in (issn_h, eissn_h):
            if h:
                value = re.sub(r"[^0-9Xx]", "", clean_text(row.get(h))).upper()
                if value:
                    identifiers.append(value)

        record = {
            "jif": clean_text(row.get(jif_h)) if jif_h else "",
            "jci": clean_text(row.get(jci_h)) if jci_h else "",
            "quartile": clean_text(row.get(quartile_h)) if quartile_h else "",
            "percentile": clean_text(row.get(percentile_h)) if percentile_h else "",
        }

        for issn in identifiers:
            metrics[issn] = record

    return metrics


def write_needed_issns(works, path="jcr_needed_issns.csv"):
    counts = Counter()
    for work in works:
        for issn in work["issns"]:
            counts[issn] += 1

    with open(path, "w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["issn", "publication_count"])
        for issn, count in sorted(counts.items()):
            writer.writerow([issn, count])

    print(f"JCR ISSN list written: {path}")


def get_jcr_for_work(work, jcr):
    for issn in work["issns"]:
        if issn in jcr:
            return jcr[issn]
    return {"jif": "", "jci": "", "quartile": "", "percentile": ""}


def first_author_is_user(work):
    if not work["authors"]:
        return False
    first = clean_text(work["authors"][0]).lower()
    return any(s in first for s in ("galán", "galan", "lacarra"))


def author_ascii(name):
    """Normalize author names to simple ASCII for robust LaTeX compilation."""
    if not name:
        return ""

    normalized = unicodedata.normalize("NFKD", str(name))
    result = "".join(
        ch for ch in normalized if not unicodedata.combining(ch)
    ).encode("ascii", "ignore").decode("ascii")

    # Normalize common German transliterations in author metadata.
    result = re.sub(r"Braeuninger", "Brauninger", result, flags=re.I)

    # Remove residual malformed markers if they occur in a name.
    result = result.replace("^?", "")
    result = re.sub(r"\s+", " ", result).strip()
    return result


def short_authors(authors, max_authors=8):
    """Format author names after ASCII normalization."""
    if not authors:
        return ""
    names = [latex_escape(author_ascii(a)) for a in authors[:max_authors]]

    if len(authors) > max_authors:
        return ", ".join(names) + ", et al."
    return ", ".join(names)


def normalize_title_for_matching(title):
    """Normalize titles for robust matching against featured.txt."""
    title = clean_text(title)
    title = unicodedata.normalize("NFKC", title)
    title = re.sub(r"\s+", " ", title).strip()
    title = title.rstrip(".")
    return title.casefold()


def read_featured_titles(path="featured.txt"):
    """Read one featured publication title per line."""
    path = Path(path)

    if not path.exists():
        return []

    titles = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            titles.append(line)

    return titles


def get_featured_works(works, featured_titles):
    """Match featured.txt titles against the ORCID publication records."""
    by_title = {
        normalize_title_for_matching(work["title"]): work
        for work in works
    }

    featured = []

    for title in featured_titles:
        key = normalize_title_for_matching(title)

        if key in by_title:
            featured.append(by_title[key])
        else:
            print(f"WARNING: Featured title not found: {title}")

    return featured


def build_tex(works, jcr, orcid, featured_works=None):
    total = len(works)
    journal_articles = sum(w["type"] == "journal-article" for w in works)
    first_author = sum(first_author_is_user(w) for w in works)
    total_citations = sum(w["citations"] for w in works)

    citation_values = sorted((w["citations"] for w in works), reverse=True)
    h_index = 0
    for i, citations in enumerate(citation_values, start=1):
        if citations >= i:
            h_index = i
        else:
            break

    years = Counter(w["year"] for w in works if w["year"])

    rows = []
    current_year = None
    for work in sorted(
        works,
        key=lambda w: (-(w["year"] or 0), w["title"].lower()),
    ):
        title = latex_escape(work["title"])
        authors = short_authors(work["authors"])
        journal = latex_escape(work["journal"])
        year = str(work["year"] or "")
        doi = work["doi"]

        jcr_data = get_jcr_for_work(work, jcr)
        jif = latex_escape(jcr_data.get("jif", ""))
        quartile = latex_escape(jcr_data.get("quartile", ""))
        percentile = latex_escape(jcr_data.get("percentile", ""))

        doi_text = ""
        if doi:
            doi_text = (
                r"\href{https://doi.org/"
                + latex_url(doi)
                + "}{"
                + latex_escape(doi)
                + "}"
            )

        row = (
            "\\Needspace{10\\baselineskip}\n"
            + r"\noindent\textbf{" + title + r"}\\" + "\n"
            + authors
            + (r"\\" + "\n" if authors else "")
            + journal
            + (f" ({year})" if year else "")
            + r"\\" + "\n"
        )

        # Remove the stray DEL control character found in one ORCID author name.
        row = row.replace("\x7f", "")

        if doi_text:
            row += "DOI: " + doi_text + r"\\" + "\n"

        row += "Citations (OpenAlex): " + str(work["citations"]) + r"\\" + "\n"

        if jif:
            row += r" \quad JIF: " + jif
        if quartile:
            row += r" \quad Quartile: " + quartile
        if percentile:
            row += r" \quad Percentile: " + percentile

        row += "\n\\medskip\n"

        # Insert a visual separator whenever the publication year changes.
        # Reserve enough vertical space so that the year heading and the
        # beginning of its first publication do not get stranded at the
        # bottom of a page.
        if year != current_year:
            if year:
                year_separator = (
                    "\\Needspace{20\\baselineskip}\n"
                    "\\vspace{0.5em}\n"
                    "\\noindent\\textbf{\\large " + year + "}\n"
                    "\\par\\noindent\\rule{\\textwidth}{0.4pt}\n"
                    "\\vspace{0.4em}\n"
                )
                row = year_separator + row

            current_year = year

        # Keep each publication together whenever possible.
        row = "\\begin{samepage}\n" + row + "\\end{samepage}\n"

        rows.append(row)

    year_text = ", ".join(
        f"{y}: {years[y]}" for y in sorted(years, reverse=True)
    )

    # Build the Featured Research Contributions section.
    featured_rows = []

    for work in (featured_works or []):
        title = latex_escape(work["title"])
        journal = latex_escape(work["journal"])
        year = str(work["year"] or "")
        doi = work["doi"]

        doi_text = ""
        if doi:
            doi_text = (
                r"\href{https://doi.org/"
                + latex_url(doi)
                + "}{"
                + latex_escape(doi)
                + "}"
            )

        featured_row = (
            r"\noindent\textbf{\large $\star$ " + title + r"}\\"
            + "\n"
        )

        if journal:
            featured_row += journal
            if year:
                featured_row += f" ({year})"
            featured_row += r"\\" + "\n"
        elif year:
            featured_row += f"{year}" + r"\\" + "\n"

        if doi_text:
            featured_row += "DOI: " + doi_text + r"\\" + "\n"

        featured_row += r"\vspace{0.5em}" + "\n"

        featured_rows.append(
            "\\begin{samepage}\n" + featured_row + "\\end{samepage}\n"
        )

    featured_section = ""
    if featured_rows:
        featured_section = (
            "\\section*{Featured Research Contributions}\n"
            + "\n".join(featured_rows)
            + "\n"
        )

    return rf"""\documentclass[a4paper,10pt]{{article}}
\usepackage[left=2.0cm,right=2.0cm,top=2.0cm,bottom=2.0cm]{{geometry}}
\usepackage{{lmodern,microtype,booktabs,enumitem,hyperref,needspace}}
\hypersetup{{colorlinks=true,urlcolor=blue,linkcolor=black}}
\setlist[itemize]{{leftmargin=*,itemsep=4pt}}
\setlength{{\parindent}}{{0pt}}
\setlength{{\parskip}}{{4pt}}

\begin{{document}}

\begin{{center}}
{{\LARGE\bfseries Javier Galán Lacarra}}\\[0.3em]
{{\Large Publication Record}}\\[0.3em]
ORCID: \href{{https://orcid.org/{latex_url(orcid)}}}{{{latex_escape(orcid)}}}\\
Metrics retrieved: {date.today().isoformat()}
\end{{center}}

\section*{{Summary}}
\begin{{tabular}}{{lr}}
\toprule
Total works & {total} \\
Journal articles & {journal_articles} \\
First-author works & {first_author} \\
Total OpenAlex citations & {total_citations} \\
OpenAlex h-index & {h_index} \\
\bottomrule
\end{{tabular}}

\section*{{Publications by Year}}
{latex_escape(year_text)}

{featured_section}
\Needspace{{15\baselineskip}}
\section*{{Full Publication Record}}

{''.join(rows)}

\section*{{Methodology}}
Publication metadata are retrieved from the author's public ORCID record.
Citation counts are retrieved from OpenAlex and correspond to the retrieval
date shown above. Journal-level metrics, when supplied, are taken from the
provided JCR export. The Journal Impact Factor is a journal-level metric and
is not an article-level measure of research quality. Code to regenerate
this document is available at https://github.com/jgalan/orcid2pdf

\end{{document}}
"""


def compile_pdf(tex_file):
    result = subprocess.run(
        ["xelatex", "-interaction=nonstopmode", "-halt-on-error", str(tex_file)],
        capture_output=True,
        text=True,
    )

    if result.returncode != 0:
        print("\n--- xelatex output ---")
        print(result.stdout[-8000:])
        if result.stderr:
            print("\n--- xelatex stderr ---")
            print(result.stderr[-3000:])
        raise RuntimeError(
            "xelatex failed. Inspect publication_record.log for the full diagnostic."
        )

    # Second pass for stable references/layout.
    subprocess.run(
        ["xelatex", "-interaction=nonstopmode", "-halt-on-error", str(tex_file)],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=True,
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--orcid", default=DEFAULT_ORCID)
    parser.add_argument("--jcr", default=None)
    parser.add_argument("--no-stats", action="store_true",
                        help="Skip OpenAlex citation statistics and h-index.")
    args = parser.parse_args()

    print("=" * 70)
    print("ORCID PUBLICATION RECORD")
    print("=" * 70)
    print(f"ORCID: {args.orcid}")

    raw = get_orcid_works(args.orcid)
    works = [normalize_work(w) for w in raw]
    works = [w for w in works if w["title"]]

    print(f"ORCID works retrieved: {len(works)}")

    write_needed_issns(works)

    if args.no_stats:
        print("Skipping OpenAlex citation statistics (--no-stats).")
        for work in works:
            work["citations"] = 0
    else:
        print("Retrieving OpenAlex citation counts...")
        add_citations(works)

    featured_titles = read_featured_titles()
    featured_works = get_featured_works(works, featured_titles)

    print(f"Featured titles requested: {len(featured_titles)}")
    print(f"Featured works matched:   {len(featured_works)}")

    jcr = {}
    if args.jcr:
        jcr = read_jcr(args.jcr)
        print(f"JCR ISSNs loaded: {len(jcr)}")
    else:
        print("No JCR CSV supplied; journal metrics will be blank.")

    tex_path = Path("publication_record.tex")
    tex_path.write_text(
        build_tex(works, jcr, args.orcid, featured_works),
        encoding="utf-8",
    )
    print(f"LaTeX created: {tex_path}")

    if shutil.which("xelatex") is None:
        print("xelatex was not found in PATH.")
        return

    compile_pdf(tex_path)
    print("PDF created: publication_record.pdf")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nInterrupted.")
        sys.exit(130)
    except Exception as exc:
        print(f"\nERROR: {exc}")
        sys.exit(1)
