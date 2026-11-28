# Reads the data files that Metacheck downloaded for each checked preprint
# and collects what they say about the participants: age, gender, ethnicity,
# country, language, education, income and so on. Run by hand, not by GitHub,
# because it reads the files.zip of each preprint from pCloud, which GitHub
# does not have (P:\Applications\metacheck\metacheck_downloads\psyarxiv).
#
# Two steps:
#  1. Reading. For each preprint, the data check's table says which data files
#     have columns about participants and which columns identify them. Those
#     files are read from the preprint's files.zip, and each file is reduced
#     to one row per distinct combination of ID values and participant
#     information, with the number of rows it stands for. The rows go into one
#     table per preprint, stored on pCloud (PARTS), never in this repository:
#     it describes individual people. ID values are replaced by a code made
#     with a secret key (KEY_FILE), so equal IDs still match across files but
#     cannot be read back. A preprint is read again only when its files.zip
#     changed (DONE_FILE).
#  2. Counting. From that table, the rules below decide who is a participant
#     and who has been counted already, and data/files_extract.json gets the
#     counts only (no individuals). scripts/totals.py adds that file to
#     data/totals.json, so the page of totals shows it after the next daily run.
#
#   python scripts/extract_files.py                read new or changed zips, then count
#   python scripts/extract_files.py --count-only   only count again from the stored table
#   python scripts/extract_files.py --redo ID ...  read only these preprint versions, again
#   python scripts/extract_files.py --limit N      read at most N preprints this time
#   python scripts/extract_files.py --check        list, per category, the columns it took and the answers
#
# Needs pandas, pyarrow, pyreadr, pyreadstat and openpyxl.

import argparse
import collections
import csv
import datetime as dt
import hashlib
import hmac
import io
import json
import os
import re
import secrets
import sys
import tempfile
import time
import zipfile

import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from update import load, load_result, save  # noqa: E402

PCLOUD_ROOT = r"P:\Applications\metacheck"            # pCloud's folder `/` of update.py's PCLOUD_FOLDER
OUT_DIR = r"P:\Applications\metacheck\participants\psyarxiv"
PARTS = os.path.join(OUT_DIR, "parts")                 # one .parquet per preprint version
DONE_FILE = os.path.join(OUT_DIR, "done.json")         # what was read, from which zip, and the problems
KEY_FILE = os.path.join(OUT_DIR, "id_key.txt")         # the secret key for the ID codes
TABLE = os.path.join(OUT_DIR, "participants.parquet")  # all parts together, for looking at by hand
CHECK_FILE = os.path.join(OUT_DIR, "check.txt")        # --check: what each category took, to look at
OUTPUT = os.path.join("data", "files_extract.json")
FORMAT = 3                     # raise when the parts change, so every preprint is read again
MAX_TEXT_BYTES = 1_000_000_000  # a .csv/.txt larger than this is not read (only its columns are kept in memory)
MAX_OTHER_BYTES = 150_000_000   # nor a larger .rds, .RData, .sav or Excel file (read whole)
MAX_IDS = 3                     # ID columns kept per file
MIN_SHARE_N = 10                # a preprint counts in the "each preprint once" charts with at least this many
MIN_VALUE_N = 5                 # a value of ethnicity, country, ... is shown when at least this many people have it
TOP_VALUES = 20

# ---- which columns are about participants -----------------------------------

# a column about someone else (a parent, a partner, a stimulus face, ...) or a
# summary of a group (a mean, an SD, a z score); matched against the column's
# name split into words
OTHER_PERSON = {"parent", "parents", "mother", "father", "mom", "mum", "dad", "caregiver", "guardian",
                "partner", "spouse", "sibling", "siblings", "dog", "pet", "target", "stim", "stimulus",
                "face", "model", "actor", "voice", "speaker", "experimenter", "confederate", "rater",
                "coder", "author", "interviewer", "avatar", "character", "vignette", "agent", "robot",
                "maternal", "paternal", "parental", "mothers", "fathers", "producer", "expert"}
SUMMARY = {"sd", "mean", "avg", "average", "z", "zscore", "std", "se", "scaled", "scale", "centered",
           "centred", "c", "cent", "pct", "percent", "prop", "proportion", "n", "count", "total",
           "min", "max", "range", "median", "sq", "squared", "log", "diff", "difference"}
FREE_TEXT = {"text", "other", "specify", "describe", "self", "open", "free", "comment", "comments",
             "string", "txt", "others"}
AGE_SKIP = {"group", "grp", "cat", "category", "bin", "band", "bracket", "onset", "first", "premier",
            "est", "estimate", "estimated", "guess", "perceived", "felt", "subjective", "discrepancy",
            "birthyear_discrepancy", "acquisition", "aoa", "cohort", "wave", "lag", "diagnosis", "lower", "upper", "bound", "residual", "resid"}
GRAMMAR = {"class", "word", "words", "stem", "article", "pronoun", "agreement", "suffix", "prefix", "lexical"}

# ID columns besides those metacheck marks as identifiers
ID_NAME = re.compile(r"prolific_?pid|prolific_?id|response_?id|worker_?id|participant|subject|"
                     r"submission_?id|(^|_)(pid|ppn|subj|subid|sub|id|code|vp|respondent)(_|$)")
# columns of trials: a file with these and no ID has several rows per person
TRIAL_NAME = re.compile(r"(^|_)(trial|trials|rt|block|stim|stimulus|item|onset|response_time|reaction_time|"
                        r"key_resp|correct|accuracy|acc)(_|$)|trials_this")


def words(name):
    # a column name as lower-case words: "Age (number only)" -> ["age", "number", "only"];
    # readr's suffix for a repeated name ("I2...4") is dropped
    name = re.sub(r"\.\.\.\d+$", "", str(name or ""))
    name = re.sub(r"([a-z])([A-Z])", r"\1_\2", name)
    return [w for w in re.split(r"[^a-z0-9]+", name.lower()) if w]


def joined(ws):
    return "_".join(ws)


def is_age(r, ws):
    if set(ws) & (OTHER_PERSON | SUMMARY | AGE_SKIP | FREE_TEXT):
        return False
    j = joined(ws)
    if r.get("concept") == "age":
        return True
    return bool(re.search(r"(^|_)(age|ages|alter|leeftijd|edad|idade|wiek|ika|alder|eta|age_in_years|"
                          r"age_years|age_months|age_in_months)(_|$)|^age(years|yrs|y|months|mos|m)$", j))


def is_gender(r, ws):
    if set(ws) & (OTHER_PERSON | SUMMARY | FREE_TEXT):
        return False
    j = joined(ws)
    if "sexual" in j or "orientation" in j:
        return False
    if set(ws) & GRAMMAR or re.search(r"noun|morpheme|grammatic", j):   # the gender of words
        return False
    if r.get("concept") == "gender":
        return True
    return bool(re.search(r"gender|(^|_)(sex|geschlecht|geslacht|sexo|sesso|kon|kjonn|sukupuoli|plec|genre)(_|$)", j))


def bare(ws):
    # the words, also without a number at their end ("caregiver1" -> "caregiver")
    return set(ws) | {re.sub(r"\d+$", "", w) for w in ws}


def simple(pattern, extra_skip=()):
    rx = re.compile(pattern)

    def test(r, ws):
        if bare(ws) & (OTHER_PERSON | SUMMARY | FREE_TEXT | set(extra_skip)):
            return False
        return bool(rx.search(joined(ws)))
    return test


def is_ethnicity(r, ws):
    if set(ws) & (OTHER_PERSON | SUMMARY | FREE_TEXT):
        return False
    return r.get("concept") == "race" or bool(re.search(r"ethnic|(^|_)(race|racial)(_|$)", joined(ws)))


CATEGORIES = [
    ("age", is_age),
    ("gender", is_gender),
    ("ethnicity", is_ethnicity),
    ("country_birth", simple(r"(country|land).*birth|birth.*(country|place)|(^|_)born")),
    ("nationality", simple(r"nationalit|citizenship")),
    ("country", simple(r"(^|_)(country|residence|land|pays|pais)(_|$)|country_of_residence|countryofresidence",
                       ("birth", "born", "code", "state", "training", "congruencia"))),
    # not the language of a task (accuracy in L1, a language switch, the language of a phrase)
    ("language", simple(r"(^|_)(language|languages|lang|native_language|first_language|mother_tongue|l1)(_|$)|"
                        r"native_?lang|first_?lang|mother_?tongue",
                        ("user", "userlanguage", "q", "acc", "score", "switch", "pair", "phrase", "full", "stroke",
                         "heartdisease", "rt", "trial", "condition"))),
    ("education", simple(r"educ|(^|_)(edu|degree|schooling|qualification)(_|$)")),
    ("income", simple(r"income|(^|_)ses(_|$)", ("ladder",))),
    ("handedness", simple(r"(^|_)(handedness|handed|hand_preference|handpref)(_|$)|handedness")),
    ("employment", simple(r"employ|occupation|(^|_)job(_|$)|work_status")),
    ("student", simple(r"(^|_)student(_|$)|student_status", ("id",))),
    ("relationship", simple(r"marital|relationship_status|(^|_)married(_|$)|civil_status")),
    ("sexual_orientation", lambda r, ws: bool(re.search(r"sexual_?orient|sexuality|sex_?orientation|(^|_)orientation(_|$)",
                                                        joined(ws)))
                           and not bare(ws) & (OTHER_PERSON | FREE_TEXT)
                           and not any(w.startswith("polit") for w in ws)),
    ("politics", simple(r"politic|ideolog")),
    ("height", simple(r"^(height|body_height|height_cm|height_in|height_m)$")),
    ("weight", simple(r"^(weight|body_weight|weight_kg|weight_lbs|weight_lb)$")),
    ("bmi", simple(r"(^|_)bmi(_|$)")),
    # added 27 November 2026 (Daniel); check them with --check before drawing them
    ("vision", simple(r"vision|eyesight|colou?r_?blind|glasses|spectacles|ishihara")),
    ("hearing", simple(r"(^|_)hearing(_|$)|deaf|hearing_aid|hearing_loss|audiogram")),
    ("religion", simple(r"relig|(^|_)(faith|church|denomination)(_|$)")),
    ("diagnosis", simple(r"(^|_)(adhd|autism|autistic|asd|dyslexia|dyslexic|disability|disabilities|disabled|"
                         r"diagnosis|diagnosed|diagnoses|neurodivergent|neurodiversity|psychiatric)(_|$)",
                         ("score", "sum", "items", "symptoms"))),
    # "speaker" is here the participant (a native speaker), not a voice; a
    # native-language column is "language"
    ("language_background", lambda r, ws: bool(re.search(r"native_?speaker|(^|_)native(_|$)|bilingual|multilingual|"
                                                         r"monolingual|proficien|(^|_)l2(_|$)|second_lang", joined(ws)))
                            and not bare(ws) & ((OTHER_PERSON - {"speaker"}) | SUMMARY | FREE_TEXT |
                                                {"user", "userlanguage", "language", "lang", "languages",
                                                 # "native" in an ethnicity (Native American, Alaska Native)
                                                 "american", "indian", "alaska", "indigenous", "race", "ethnicity",
                                                 "ethnic", "hawaiian", "peru", "pe", "stroke"})
                            and "indigenous" not in joined(ws)),
    ("children_household", simple(r"(^|_)(children|kids|n_children|num_children|number_of_children|household|"
                                  r"household_size|hh_size)(_|$)|has_?children|num_?kids", ("income",))),
    # the Cantril ladder and a "peak event" ladder measure well-being, not social status
    ("ses_ladder", lambda r, ws: bool(re.search(r"ladder|mac_?arthur|social_status|subjective_ses|subjective_social",
                                                joined(ws)))
                   and not re.search(r"cantril|peak|event|life|awe", joined(ws))
                   and not bare(ws) & (OTHER_PERSON | SUMMARY | FREE_TEXT)),
    ("study_field", simple(r"(^|_)(major|faculty|discipline|field_of_study|study_field|field_study|study_program|"
                           r"study_programme|programme|program_of_study|subject_of_study)(_|$)",
                           ("trip", "before", "taking"))),
    # smoking and alcohol, region and location, latitude and longitude were
    # tried on 27 November 2026 and dropped (Daniel): mostly questionnaire
    # items, codes and task variables, and coordinates in only 2 preprints
]
CAT_NAMES = [c for c, _ in CATEGORIES]
# categories whose values are numbers to keep as they are (not "a number code")
NUMERIC = {"height", "weight", "bmi", "income", "children_household", "ses_ladder"}
# numbers with decimals are fine here (elsewhere they are scores, not answers)
DECIMALS = {"height", "weight", "bmi", "income"}
# categories rounded to whole numbers, also in the stored table (none since
# latitude and longitude were dropped)
ROUNDED = set()


def platforms(names, is_qualtrics):
    # where the participants came from, by the columns the file has
    j = " ".join(joined(words(n)) for n in names)
    out = set()
    if "prolific" in j or ("submission_id" in j and "total_approvals" in j):
        out.add("Prolific")
    if re.search(r"worker_?id|mturk|assignment_?id|hit_?id", j):
        out.add("MTurk")
    if "sona" in j:
        out.add("SONA")
    if "cloudresearch" in j or "turkprime" in j:
        out.add("CloudResearch")
    if is_qualtrics:
        out.add("Qualtrics")
    return sorted(out)


# ---- standard forms -----------------------------------------------------------

NUMBER = re.compile(r"^\s*(\d+(?:[.,]\d+)?)\s*(years?|yrs?|y|jaar|jahre|ans|años|anos|lat)?\.?\s*$", re.I)


def age_unit(column):
    ws = words(column)
    j = joined(ws)
    if re.search(r"month|mnth|(^|_)mos(_|$)|(^|_)m$|^agem$|^age_?m$", j):
        return "months"
    if re.search(r"(^|_)days?(_|$)", j):
        return "days"
    if re.search(r"birth|(^|_)yob(_|$)|born|year_of", j):
        return "birth year"
    if re.search(r"year|(^|_)(yrs?|y|jaar|jahre|ans)(_|$)|^age_?y", j):
        return "years (named)"
    return "years"


def to_number(v):
    if v is None:
        return None
    m = NUMBER.match(str(v))
    return float(m.group(1).replace(",", ".")) if m else None


# a preprint about animals (its title) is not read; a preprint whose
# participants are on average younger than CHILD_AGE counts with their ages
# only when its title or abstract speaks of children (otherwise the "ages"
# are mostly codes of age bands: 1 = 18-24, 2 = 25-34, ...). The same as in
# totals.py.
ANIMALS = re.compile(r"\b(dogs?|canines?|cats?|felines?|mice|mouse|rats?|rodents?|primates?|monkeys?|macaques?|"
                     r"chimpanzees?|apes|birds?|fish|species|animals?|horses?|pigs?|cows?|cattle|sheep)\b", re.I)
CHILDREN = re.compile(r"\b(child|children|childhood|kids?|infants?|infancy|toddlers?|preschool\w*|kindergarten\w*|"
                      r"pupils?|school.?aged?|adolescen\w*|youths?|teens?|teenagers?|boys|girls|"
                      r"\w+.months?.olds?|\w+.years?.olds?|grades?|developmental)\b", re.I)
CHILD_AGE = 16


def title_abstract(result, title):
    paper = result.get("paper") or {}
    abstract = {s.get("section_id") for s in paper.get("section") or [] if s.get("section_type") == "abstract"}
    return " ".join([str(title or "")] + [str(t.get("text") or "") for t in paper.get("text") or []
                                          if t.get("section_id") in abstract])


MONTHS_IN_TEXT = re.compile(r"\d\s*(-|–|to)?\s*\d*\s*-?\s*months?[- ]olds?\b|months? of age|age in months|"
                            r"aged \d+\s*(-|–|to)\s*\d+\s*months", re.I)


def ages_in_years(values, column, year, months_in_text):
    # the values of one age column in years, and the unit they were in; a
    # range such as "18-24" is not a number and stays only as written. A
    # column named just "age" whose values could be months of young children
    # or years of adults (median 6 to 72) in a paper that gives ages in months
    # has an unclear unit: parents of 18-month-olds are about 30 as well
    nums = [to_number(v) for v in values]
    unit = age_unit(column)
    known_n = sorted(n for n in nums if n is not None)
    mid = known_n[len(known_n) // 2] if known_n else None
    if unit == "years" and mid is not None and 1900 <= mid <= 2030:
        unit = "birth year"
    elif unit == "years" and mid is not None and months_in_text and 6 <= mid <= 72:
        unit = "unclear"
    if known_n and known_n[0] < 0:
        unit = "not ages"       # centred or scaled: an age is never below zero
    unit = "years" if unit == "years (named)" else unit
    out = []
    for n in nums:
        if n is None or unit in ("unclear", "not ages"):
            out.append(None)
            continue
        a = {"months": n / 12, "days": n / 365.25, "birth year": (year - n) if year else None}.get(unit, n)
        out.append(round(a, 2) if a is not None and 0 < a <= 110 else None)
    return out, unit


GENDER_RULES = [
    ("not given", r"prefer not|rather not|no answer|not say|not to say|decline|unknown|^n/?a$|missing|keine angabe|"
                  r"weet niet|want to answer|no response|prefiero no|prefer no|não quero|prefernottosay|^pna$|"
                  r"do not wish|wish to provide|不愿透露"),
    ("other", r"non.?binary|nonbinary|binari|binär|enby|genderqueer|gender.?fluid|agender|divers|^div$|other|third|"
              r"trans|two.?spirit|self.?describ|queer|^x$|^nb$|anders|andere|autre|otro|altro|annat|conforming|"
              r"neither|intersex|not.?listed|identify as"),
    ("woman", r"^(f|fem|femal|female|females|woman|women|girl|w|weiblich|frau|vrouw|v|vrouwelijk|femme|f[ée]minin|"
              r"femenino|femenina|mujer|kvinna|kvinde|kvinne|nainen|donna|femmina|kobieta|feminino|mulher|"
              r"cis(gender)?.?(female|woman))\b|^(女|女性|여|여자|여성)$"),
    ("man", r"^(m|h|male|males|man|men|boy|männlich|maennlich|mann|homme|masculin|masculino|hombre|mand|mies|uomo|"
            r"maschio|mężczyzna|homem|mannelijk|cis(gender)?.?(male|man))\b|^(男|男性|남|남자|남성)$"),
]


def gender_std(v):
    if v is None or not str(v).strip():
        return None
    s = str(v).strip().lower()
    if re.fullmatch(r"-?\d+(\.0+)?", s):
        return "coded"                 # a number without a label saying what it means
    for name, rx in GENDER_RULES:
        if re.search(rx, s):
            return name
    return "unrecognised"


COUNTRY_SAME = {"us": "united states", "usa": "united states", "u.s.": "united states", "u.s.a.": "united states",
                "united states of america": "united states", "america": "united states",
                "uk": "united kingdom", "u.k.": "united kingdom", "great britain": "united kingdom",
                "england": "united kingdom", "scotland": "united kingdom", "wales": "united kingdom",
                "the netherlands": "netherlands", "holland": "netherlands", "nederland": "netherlands",
                "deutschland": "germany", "czechia": "czech republic", "türkiye": "turkey", "turkiye": "turkey",
                "united kingdom of great britain and northern ireland": "united kingdom", "belgien": "belgium",
                "belgië": "belgium", "belgique": "belgium", "schweiz": "switzerland", "suisse": "switzerland",
                "österreich": "austria", "italia": "italy", "españa": "spain", "polska": "poland",
                "russland": "russia", "russian federation": "russia", "korea": "south korea",
                "republic of korea": "south korea", "south korea": "south korea"}
# a nationality written as an adjective, as the country (for the world map)
for _country, _words in {
        "united kingdom": "british english scottish welsh", "germany": "german deutsch", "netherlands": "dutch",
        "united states": "american us-american", "italy": "italian italiana italiano italienisch", "france": "french",
        "spain": "spanish", "poland": "polish", "china": "chinese", "india": "indian", "canada": "canadian",
        "australia": "australian", "ireland": "irish", "portugal": "portuguese", "greece": "greek",
        "belgium": "belgian", "switzerland": "swiss schweizerisch", "austria": "austrian österreichisch",
        "sweden": "swedish", "nigeria": "nigerian", "south africa": "south-african", "turkey": "turkish",
        "russia": "russian", "japan": "japanese", "south korea": "korean south-korean", "mexico": "mexican",
        "brazil": "brazilian", "hungary": "hungarian", "romania": "romanian", "czech republic": "czech",
        "denmark": "danish", "norway": "norwegian", "finland": "finnish", "kenya": "kenyan", "pakistan": "pakistani",
        "iran": "iranian", "israel": "israeli", "new zealand": "new-zealander kiwi", "zimbabwe": "zimbabwean",
        "egypt": "egyptian", "ukraine": "ukrainian", "croatia": "croatian", "serbia": "serbian", "slovakia": "slovak",
        "slovenia": "slovenian", "bulgaria": "bulgarian", "lithuania": "lithuanian", "latvia": "latvian",
        "estonia": "estonian", "colombia": "colombian", "chile": "chilean", "argentina": "argentinian argentine",
        "peru": "peruvian", "ghana": "ghanaian", "philippines": "filipino filipina", "indonesia": "indonesian",
        "malaysia": "malaysian", "vietnam": "vietnamese", "thailand": "thai", "bangladesh": "bangladeshi",
        "singapore": "singaporean", "luxembourg": "luxembourgish", "iceland": "icelandic", "cyprus": "cypriot"}.items():
    for _w in _words.split():
        COUNTRY_SAME.setdefault(_w.replace("-", " "), _country)
# two-letter country codes (not "no": in a country column it is mostly the answer no)
for _code, _country in {"de": "germany", "nl": "netherlands", "be": "belgium", "fr": "france", "it": "italy",
                        "es": "spain", "pl": "poland", "ch": "switzerland", "at": "austria", "se": "sweden",
                        "dk": "denmark", "fi": "finland", "ie": "ireland", "pt": "portugal", "gr": "greece",
                        "cz": "czech republic", "hu": "hungary", "ro": "romania", "au": "australia",
                        "nz": "new zealand", "ca": "canada", "cn": "china", "jp": "japan", "br": "brazil",
                        "mx": "mexico", "za": "south africa", "gb": "united kingdom"}.items():
    COUNTRY_SAME.setdefault(_code, _country)
COUNTRY_SAME["south african"] = "south africa"
COUNTRY_SAME["new zealander"] = "new zealand"


# the same answer spelled in several ways, per category (the key without
# punctuation)
SAME = {
    "language": {"en": "english", "eng": "english", "engl": "english", "englisch": "english", "de": "german",
                 "deu": "german", "ger": "german", "deutsch": "german", "nl": "dutch", "nederlands": "dutch",
                 "fr": "french", "francais": "french", "français": "french", "es": "spanish", "espanol": "spanish",
                 "español": "spanish", "it": "italian", "italiano": "italian", "pl": "polish", "polski": "polish"},
    "ethnicity": {"black": "black or african american", "african american": "black or african american",
                  "black african american": "black or african american", "blackafrican american": "black or african american",
                  "caucasian": "white", "white or caucasian": "white", "whitecaucasian": "white", "white caucasian": "white",
                  "asian american": "asian", "hispanic": "hispanic or latino", "latino": "hispanic or latino",
                  "latina": "hispanic or latino", "latinx": "hispanic or latino", "latinoa": "hispanic or latino",
                  "hispaniclatino": "hispanic or latino", "hispanic latino": "hispanic or latino",
                  "hispanic or latinoa": "hispanic or latino"},
    "education": {"bachelors": "bachelor's degree", "bachelor": "bachelor's degree", "bachelors degree": "bachelor's degree",
                  "bachelor degree": "bachelor's degree", "masters": "master's degree", "master": "master's degree",
                  "masters degree": "master's degree", "master degree": "master's degree",
                  "high school": "high school graduate", "high school diploma": "high school graduate",
                  "phd": "doctorate", "doctoral degree": "doctorate", "doctorate degree": "doctorate",
                  "doctorate degree phdother": "doctorate"},
    "handedness": {"r": "right", "right handed": "right", "righthanded": "right", "rechts": "right",
                   "rechtshänder": "right", "rechtshändig": "right", "l": "left", "left handed": "left",
                   "lefthanded": "left", "links": "left", "linkshänder": "left", "linkshändig": "left",
                   "b": "ambidextrous", "both": "ambidextrous", "beidhändig": "ambidextrous", "mixed": "ambidextrous",
                   "ambidexterous": "ambidextrous"},
    "relationship": {"married": "married or partnership", "married living together": "married or partnership",
                     "married or domestic partnership": "married or partnership",
                     "married or in a registered partnership": "married or partnership",
                     "marrieddomestic partnership": "married or partnership", "partnership": "married or partnership",
                     "single never married": "single", "single  never married": "single", "never married": "single",
                     "divorced": "divorced or separated", "separated": "divorced or separated",
                     "singledivorced": "divorced or separated", "single divorced": "divorced or separated"},
    "student": {"true": "yes", "y": "yes", "ja": "yes", "false": "no", "n": "no", "nein": "no"},
    "sexual_orientation": {"straight": "heterosexual", "gay": "gay or lesbian", "lesbian": "gay or lesbian",
                           "gaylesbian": "gay or lesbian", "homosexual": "gay or lesbian",
                           "other": "other", "other sexual orientation": "other"},
}


def value_std(cat, v):
    # ethnicity, country, ...: as written, in lower case, with spaces tidied;
    # a bare number is a code whose meaning the file does not give
    if v is None or not str(v).strip():
        return None
    s = re.sub(r"\s+", " ", str(v).strip().lower())
    if cat in ROUNDED:
        n = to_number(s.lstrip("-"))
        return None if n is None else str(round(n * (-1 if s.startswith("-") else 1)))
    # a number, or several (a question with more than one answer: "1,3")
    if re.fullmatch(r"-?\d+(\.0+)?|\d+([,;|/ ]+\d+)+", s) and cat not in NUMERIC:
        return "(a number code)"
    if cat in ("country", "country_birth", "nationality"):
        s = COUNTRY_SAME.get(s, COUNTRY_SAME.get(s.replace("-", " "), s))
    key = re.sub(r"[^\w ]", "", s).strip()
    s = SAME.get(cat, {}).get(key, s)
    # a single letter left after the spellings above ("r" is right-handed) is
    # a code that differs between studies ("w" may be White, but in another
    # study "h" is White and "c" Black)
    if len(s) == 1 and s.isalpha():
        return "(a letter code)"
    return s[:60]


# ---- reading one file from a zip ----------------------------------------------

def clean_name(source_file):
    # metacheck's file name without the sheet ("x.xlsx [data]"), a repeat
    # number ("x.csv #1") or the repository address before it ("overview?...: data/x.csv")
    s = re.sub(r" \[[^\]]*\]$", "", str(source_file))
    s = re.sub(r" #\d+$", "", s)
    if ": " in s:
        s = s.split(": ", 1)[1]
    return s.replace("\\", "/")


def sheet_of(source_file, sheet):
    if sheet:
        return sheet
    m = re.search(r" \[([^\]]*)\]$", str(source_file))
    return m.group(1) if m else None


def find_entry(names, source_file, repo_url):
    # the file's place in the zip, under downloaded/ (the repository as it
    # was downloaded); when one repository was downloaded twice under two
    # addresses, the folder whose name shares the most with the address
    s = clean_name(source_file)
    found = [n for n in names if n.startswith("downloaded/") and n.endswith("/" + s)]
    if not found:
        return None
    url_words = set(re.findall(r"[a-z0-9]+", str(repo_url or "").lower()))
    return max(found, key=lambda n: len(url_words & set(re.findall(r"[a-z0-9]+", n.split("/")[1].lower()))))


def norm(name):
    return re.sub(r"[^a-z0-9]", "", re.sub(r"\.\.\.\d+$", "", str(name)).lower())


def read_text(data, wanted, ext):
    text = None
    for enc in ("utf-8-sig", "cp1252", "latin-1"):
        try:
            text = data.decode(enc)
            break
        except UnicodeDecodeError:
            continue
    head = text[:20000]
    try:
        sep = csv.Sniffer().sniff(head, delimiters=",;\t|").delimiter
    except csv.Error:
        sep = "\t" if ext in (".tsv", ".txt") and "\t" in head else ("," if "," in head else r"\s+")
    return pd.read_csv(io.StringIO(text), sep=sep, dtype=str, keep_default_na=False, on_bad_lines="skip",
                       engine="python" if sep == r"\s+" else "c",
                       usecols=lambda c: norm(c) in wanted)


def read_member(z, entry, sheet, wanted):
    # the file as a table of text with only the wanted columns, or a reason it
    # could not be read
    info = z.getinfo(entry)
    ext = os.path.splitext(entry)[1].lower()
    limit = MAX_TEXT_BYTES if ext in (".csv", ".tsv", ".txt", ".dat") else MAX_OTHER_BYTES
    if info.file_size > limit:
        return None, "too large (%d MB)" % (info.file_size // 1_000_000)
    if ext in (".csv", ".tsv", ".txt", ".dat"):
        return read_text(z.read(entry), wanted, ext), None
    if ext in (".xlsx", ".xlsm"):
        book = pd.ExcelFile(io.BytesIO(z.read(entry)), engine="openpyxl")
        name = sheet if sheet in book.sheet_names else next(
            (s for s in book.sheet_names if sheet and s.lower() == sheet.lower()), book.sheet_names[0])
        return book.parse(name, dtype=str), None
    if ext in (".sav", ".zsav", ".por", ".rds", ".rdata", ".rda", ".dta"):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "f" + ext)
            with open(path, "wb") as f:
                f.write(z.read(entry))
            if ext in (".sav", ".zsav", ".por"):
                import pyreadstat
                reader = pyreadstat.read_por if ext == ".por" else pyreadstat.read_sav
                _, meta = reader(path, metadataonly=True)
                cols = [c for c in meta.column_names if norm(c) in wanted]
                if not cols:
                    return None, "columns not found in the file"
                # with the value labels, so a coded gender says what it is
                df, _ = reader(path, usecols=cols, apply_value_formats=True)
                return df, None
            if ext == ".dta":
                return pd.read_stata(path, convert_categoricals=True), None
            import pyreadr
            frames = [f for f in pyreadr.read_r(path).values() if isinstance(f, pd.DataFrame)]
            if not frames:
                return None, "no table in the R file"
            # the object holding most of the wanted columns (factors keep their labels)
            return max(frames, key=lambda f: len({norm(c) for c in f.columns} & wanted)), None
    return None, "file type not read (%s)" % ext


# written for "no answer": a missing value, not an answer (and not an ID: a
# file whose ID column says "NA" in many rows would otherwise make them one person)
MISSING = {"na", "n/a", "nan", "null", "#n/a", "missing", ".", "-", "--", "-9", "-99", "-999", "-9999",
           "data_expired", "consent_revoked", "consent revoked", "#null!", "none given", "not available",
           "not reported"}


def as_text(series):
    def one(v):
        if v is None or (isinstance(v, float) and v != v) or pd.isna(v):
            return None
        s = str(v).strip()
        if isinstance(v, float) and v.is_integer():
            s = str(int(v))
        if s.lower() in MISSING:
            return None
        return s or None
    return [one(v) for v in series.astype(object)]


# ---- step 1: reading a preprint ----------------------------------------------

def id_code(key, value):
    return None if value is None else hmac.new(key, value.encode("utf-8"), hashlib.sha256).hexdigest()[:16]


def file_plan(rows):
    # from the data check's rows of one file: the column chosen for each
    # category (the one named most plainly when there are several) and the
    # ID columns (most distinct values first)
    chosen = {}
    for cat, test in CATEGORIES:
        hits = [r for r in rows if r.get("representation") != "empty" and test(r, words(r.get("column_name")))]
        if hits:
            exact = [r for r in hits if joined(words(r["column_name"])) == cat]
            chosen[cat] = (exact or sorted(hits, key=lambda r: len(str(r["column_name"]))))[0]["column_name"]
    used = set(chosen.values())
    ids = [r for r in rows if r.get("column_name") not in used and r.get("representation") != "empty" and
           (r.get("role") == "identifier" or r.get("concept") == "id" or ID_NAME.search(joined(words(r.get("column_name")))))]
    ids = sorted(ids, key=lambda r: -(r.get("n_unique") or 0))[:MAX_IDS]
    return chosen, [r["column_name"] for r in ids]


def read_preprint(osf_id, result, key, year, title):
    # the rows of one preprint version, and the problems met
    table = ((result.get("modules") or {}).get("data_check") or {}).get("table")
    if not isinstance(table, list):
        return [], []
    if ANIMALS.search(str(title or "")):
        return [], [{"file": None, "reason": "about animals"}]
    children = bool(CHILDREN.search(title_abstract(result, title)))
    by_file = collections.defaultdict(list)
    for r in table:
        if isinstance(r, dict) and r.get("column_name") is not None:
            by_file[(r.get("repo_url"), r.get("source_file"), r.get("sheet"))].append(r)
    zip_path = zip_of(result)
    months_in_text = bool(MONTHS_IN_TEXT.search(json.dumps(result.get("paper") or {}, ensure_ascii=False)))
    out, problems = [], []
    with zipfile.ZipFile(zip_path) as z:
        names = z.namelist()
        for (repo_url, source_file, sheet), rows in by_file.items():
            chosen, id_cols = file_plan(rows)
            # a file about participants has their age, gender or ethnicity; a
            # file with only a country or language column is mostly a table of
            # countries or languages, not of people
            if not chosen.keys() & {"age", "gender", "ethnicity"}:
                continue
            entry = find_entry(names, source_file, repo_url)
            if not entry:
                problems.append({"file": source_file, "reason": "not in files.zip"})
                continue
            wanted = {norm(c) for c in list(chosen.values()) + id_cols}
            try:
                df, why = read_member(z, entry, sheet_of(source_file, sheet), wanted)
            except Exception as e:                      # a file that will not open
                df, why = None, "could not be read: %s" % str(e)[:150]
            if df is None:
                problems.append({"file": source_file, "reason": why})
                continue
            cols = {}
            for c in df.columns:
                cols.setdefault(norm(c), c)
            first = rows[0]
            is_q = bool(first.get("is_qualtrics"))
            take = {name: cols.get(norm(name)) for name in list(chosen.values()) + id_cols}
            if not any(take[c] for c in chosen.values()):
                problems.append({"file": source_file, "reason": "columns not found in the file"})
                continue
            part = pd.DataFrame({name: as_text(df[col]) if col is not None else [None] * len(df)
                                 for name, col in take.items()}, dtype=object)
            # Qualtrics' two rows under the names: the question and its ImportId
            if is_q and len(part) >= 2 and any(str(v or "").startswith('{"ImportId') for v in part.iloc[1]):
                part = part.iloc[2:]
            if not len(part):
                continue
            grouped = part.groupby(list(part.columns), dropna=False, sort=False).size().reset_index(name="n_rows")
            has_trials = bool(TRIAL_NAME.search(" ".join(joined(words(r.get("column_name"))) for r in rows))) or \
                any(r.get("concept") in ("reaction_time", "accuracy") for r in rows)
            base = {"preprint": osf_id, "repo_url": repo_url, "entry": entry, "folder": os.path.dirname(entry),
                    "file": os.path.basename(entry), "sheet": sheet_of(source_file, sheet),
                    "group": first.get("group"), "has_trials": has_trials, "children_in_text": children,
                    "platforms": ",".join(platforms([r.get("column_name") for r in rows], is_q))}
            g = {c: [None if (v is None or v != v) else v for v in grouped[c]] for c in grouped.columns}
            ages, unit = ages_in_years(g[chosen["age"]], chosen["age"], year, months_in_text) if "age" in chosen else (None, None)
            for i in range(len(grouped)):
                row = dict(base, n_rows=int(grouped["n_rows"].iloc[i]))
                for k in range(MAX_IDS):
                    name = id_cols[k] if k < len(id_cols) else None
                    row["id%d_name" % (k + 1)] = name
                    row["id%d" % (k + 1)] = id_code(key, g[name][i]) if name else None
                for cat in CAT_NAMES:
                    col = chosen.get(cat)
                    raw = g[col][i] if col else None
                    if cat in ROUNDED:
                        raw = value_std(cat, raw)
                    row[cat + "_col"] = col
                    row[cat + "_raw"] = raw
                    if cat == "age":
                        row["age_unit"] = unit if col else None
                        row["age_years"] = ages[i] if col else None
                    elif cat == "gender":
                        row["gender_std"] = gender_std(raw)
                    else:
                        row[cat + "_std"] = value_std(cat, raw)
                out.append(row)
    return out, problems


def zip_of(result):
    folder = ((result.get("pcloud") or {}).get("folder") or "").lstrip("/")
    name = (result.get("pcloud") or {}).get("files_zip")
    return os.path.join(PCLOUD_ROOT, *folder.split("/"), name) if folder and name else None


def save_done(done):
    # the pCloud drive sometimes refuses to replace a file it is still
    # uploading; try again for up to a minute
    for attempt in range(12):
        try:
            save(DONE_FILE, done)
            return
        except PermissionError:
            time.sleep(5)
    save(DONE_FILE, done)


def secret_key():
    if not os.path.exists(KEY_FILE):
        with open(KEY_FILE, "w") as f:
            f.write(secrets.token_hex(32))
    with open(KEY_FILE) as f:
        return bytes.fromhex(f.read().strip())


def newest_with_zip(index, data_dir):
    # per preprint, its newest version whose files.zip is on pCloud, with
    # its result (made by any version of metacheck)
    by_base = collections.defaultdict(list)
    for item in index:
        by_base[item.get("base_id") or item["id"].split("_v")[0]].append(item)
    out = []
    for base, items in by_base.items():
        for item in sorted(items, key=lambda i: -(i.get("version") or 0)):
            result = load_result(os.path.join(data_dir, "papers"), item["id"])
            path = zip_of(result) if result else None
            if path and os.path.exists(path):
                out.append((item, result, path))
                break
    return out


def read_all(args, index, key):
    os.makedirs(PARTS, exist_ok=True)
    done = load(DONE_FILE, {})
    todo = newest_with_zip(index, args.data_dir)
    keep = {item["id"] for item, _, _ in todo}
    # a part of an older version, once a newer version is read, is not counted
    for f in os.listdir(PARTS):
        if f.endswith(".parquet") and f[:-8] not in keep:
            os.replace(os.path.join(PARTS, f), os.path.join(PARTS, f + ".old"))
            done.pop(f[:-8], None)
    n = 0
    for item, result, path in todo:
        osf_id = item["id"]
        st = os.stat(path)
        was = done.get(osf_id) or {}
        if args.redo and osf_id not in args.redo:
            continue
        if osf_id not in args.redo and was.get("format") == FORMAT and was.get("zip_mtime") == st.st_mtime \
                and was.get("zip_size") == st.st_size:
            continue
        if args.limit and n >= args.limit:
            break
        n += 1
        t0 = time.time()
        year = int(str(item.get("published") or "2026")[:4])
        try:
            rows, problems = read_preprint(osf_id, result, key, year, item.get("title"))
        except Exception as e:                           # a zip that will not open
            rows, problems = [], [{"file": None, "reason": "files.zip could not be read: %s" % str(e)[:150]}]
        part = os.path.join(PARTS, osf_id + ".parquet")
        if rows:
            try:
                df = pd.DataFrame(rows)
                df["metacheck_version"] = result.get("metacheck_version")
                df.to_parquet(part, index=False)
            except MemoryError:                          # pyarrow's ArrowMemoryError is one
                # (medRxiv: national registers of patients, 1.7 million rows
                # of counts per practice and area)
                problems.append({"file": None, "reason": "too many rows to hold in memory: %d" % len(rows)})
                rows = []
            df = None
        if not rows and os.path.exists(part):
            os.remove(part)
        done[osf_id] = {"format": FORMAT, "zip_mtime": st.st_mtime, "zip_size": st.st_size, "rows": len(rows),
                        "files": len({r["entry"] for r in rows}), "problems": problems,
                        "read": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}
        save_done(done)
        print("%s: %d rows from %d files, %d problems, %.0f s" % (
            osf_id, len(rows), done[osf_id]["files"], len(problems), time.time() - t0), flush=True)
    print("read %d preprints" % n)


# ---- step 2: counting ----------------------------------------------------------

def known(v):
    # None for a missing value (the stored table has NaN for those)
    return None if v is None or (isinstance(v, float) and v != v) else v


def first_known(values):
    for v in values:
        if known(v) is not None:
            return v
    return None


def file_people(f):
    # the participants in one file: (kind, people), where people is a list of
    # dicts {codes: set of ID codes, info..., w: how many people it stands for}
    info_cols = ["age_years", "gender_std"] + [c + "_std" for c in CAT_NAMES if c not in ("age", "gender")]
    # without ages, a "gender" column must mostly hold people's genders (not,
    # for instance, the grammatical gender of words)
    if f["age_years"].isna().all() and not (f["age_unit"] == "unclear").any():
        g = f["gender_std"].dropna()
        if not len(g) or g.isin(["woman", "man", "other", "not given"]).mean() < 0.5:
            return "not people", [], None
    check = "age_years" if f["age_years"].notna().any() else ("gender_std" if f["gender_std"].notna().any() else None)
    # the participant ID: among the ID columns under which each value has
    # ages within 3 years of each other (people tested more than once) or a
    # single gender, the one with the fewest values; a column that numbers
    # trials also passes, but has more values, and one that numbers groups or
    # conditions has ages decades apart
    best = None
    for k in range(1, MAX_IDS + 1):
        col = "id%d" % k
        if col not in f or f[col].isna().all():
            continue
        vals = f[col].dropna()
        nv = vals.nunique()
        if check:
            by = f.dropna(subset=[col]).groupby(col)[check]
            per = (by.max() - by.min() <= 3) if check == "age_years" else (by.nunique(dropna=True) <= 1)
            if per.mean() < 0.95:
                continue
        if best is None or nv < best[1]:
            best = (col, nv)
    if best:
        col, nv = best
        # other ID columns with about as many values name the same people
        # (a Qualtrics ResponseId next to a PROLIFIC_PID)
        alias = [c for c in ("id1", "id2", "id3") if c != col and c in f and f[c].notna().any()
                 and 0.9 * nv <= f[c].nunique() <= 1.1 * nv]
        people = []
        for code, g in f.dropna(subset=[col]).groupby(col, sort=False):
            codes = {code} | {v for a in alias for v in g[a].dropna().unique()}
            p = {c: known(first_known(g[c].tolist())) for c in info_cols}
            # the first age is kept; noted when the person has several
            p.update(codes=codes, w=1, several_ages=g["age_years"].nunique() > 1)
            people.append(p)
        return "id", people, f["id%s_name" % col[-1]].iloc[0]
    answers = f[info_cols].drop_duplicates()
    if all(known(v) is None for v in answers.to_numpy().ravel()):
        return "empty", [], None        # the columns are there, the answers are not
    if len(answers) == 1:               # one person per file (the same answers in every row)
        p = {c: known(answers[c].iloc[0]) for c in info_cols}
        p.update(codes=set(), w=1)
        return "single", [p], None
    if f["has_trials"].iloc[0]:
        return "trials", [], None       # several rows per person, and nothing says whose
    people = []
    for _, r in f.iterrows():
        p = {c: known(r[c]) for c in info_cols}
        p.update(codes=set(), w=int(r["n_rows"]))
        people.append(p)
    return "rows", people, None


def agree(a, b):
    # people with the same ID code in two files: the same people when their
    # ages (within a year) or genders agree for 90% of those where both are known
    pairs = [(x, y) for x, y in zip(a, b) if x is not None and y is not None]
    if not pairs:
        return True
    same = sum(1 for x, y in pairs if (abs(x - y) <= 1.01 if isinstance(x, float) and isinstance(y, float) else x == y))
    return same / len(pairs) >= 0.9


def weighted_median(pairs):
    pairs = sorted(pairs)
    half, run = sum(w for _, w in pairs) / 2, 0
    for v, w in pairs:
        run += w
        if run >= half:
            return v
    return None


class Union:
    def __init__(self):
        self.up = {}

    def find(self, x):
        self.up.setdefault(x, x)
        while self.up[x] != x:
            self.up[x] = self.up[self.up[x]]
            x = self.up[x]
        return x

    def join(self, a, b):
        self.up[self.find(a)] = self.find(b)


def preprint_people(d):
    # the participants of one preprint, each counted once (see NOTES.md):
    #  - in a file, one person per participant ID; without an ID, one person
    #    per file when every row says the same, none when the rows are trials,
    #    otherwise one per row;
    #  - files whose IDs overlap (half the smaller file's people, with ages
    #    that agree) hold the same people, joined by their ID codes;
    #  - per study group, sets of people under the same kind of ID that do
    #    not overlap are different people and are added; a set under another
    #    kind of ID cannot be matched and is left out when the group already
    #    has a larger set; a set without IDs counts only in a group without
    #    any set with IDs, and then only the largest
    files, why = [], collections.Counter()
    for entry, f in d.groupby(["entry", "sheet"], dropna=False, sort=False):
        kind, people, id_name = file_people(f)
        why[kind] += 1
        if people:
            files.append({"entry": entry[0], "folder": f["folder"].iloc[0], "group": known(f["group"].iloc[0]),
                          "kind": kind, "people": people, "id_name": id_name,
                          "codes": {c for p in people for c in p["codes"]}})
    idf = [f for f in files if f["kind"] == "id"]
    u = Union()
    for i, a in enumerate(idf):
        u.find(i)
        for j in range(i):
            b = idf[j]
            common = a["codes"] & b["codes"]
            if len(common) < 0.5 * min(len(a["people"]), len(b["people"])) or not common:
                continue
            pa = {c: p for p in a["people"] for c in p["codes"]}
            pb = {c: p for p in b["people"] for c in p["codes"]}
            key = "age_years" if any(pa[c]["age_years"] is not None for c in common) else "gender_std"
            if agree([pa[c][key] for c in common], [pb[c][key] for c in common]):
                u.join(i, j)
    sets = []                                   # {group, id_names, people}
    clusters = collections.defaultdict(list)
    for i, f in enumerate(idf):
        clusters[u.find(i)].append(f)
    for members in clusters.values():
        members.sort(key=lambda f: -len(f["people"]))
        pu = Union()
        for f in members:
            for k, p in enumerate(f["people"]):
                node = (f["entry"], k)
                for c in p["codes"]:
                    pu.join(node, ("code", c))
        merged = collections.OrderedDict()
        for f in members:
            for k, p in enumerate(f["people"]):
                root = pu.find((f["entry"], k))
                if root not in merged:
                    merged[root] = dict(p)
                else:
                    for c, v in p.items():
                        if merged[root].get(c) is None and c not in ("codes", "w"):
                            merged[root][c] = v
        groups = collections.Counter(f["group"] for f in members)
        sets.append({"group": groups.most_common(1)[0][0], "ids": {f["id_name"] for f in members},
                     "people": list(merged.values()), "with_id": True})
    singles = collections.defaultdict(list)
    for f in files:
        if f["kind"] == "single":
            singles[(f["group"], f["folder"])].extend(f["people"])
        elif f["kind"] == "rows":
            sets.append({"group": f["group"], "ids": set(), "people": f["people"], "with_id": False})
    for (group, _), people in singles.items():
        sets.append({"group": group, "ids": set(), "people": people, "with_id": False})
    kept = []
    by_group = collections.defaultdict(list)
    for s in sets:
        by_group[s["group"]].append(s)
    for group, ss in by_group.items():
        ss.sort(key=lambda s: -sum(p["w"] for p in s["people"]))
        with_id = [s for s in ss if s["with_id"]]
        if with_id:
            chosen = [with_id[0]]
            for s in with_id[1:]:
                if any(s["ids"] & c["ids"] for c in chosen):
                    chosen.append(s)
            kept.extend(chosen)
        else:
            kept.append(ss[0])
    return [p for s in kept for p in s["people"]], why


LIKERT = re.compile(r"\b(?:agree|disagree|neutral|strongly|slightly|somewhat|siempre|nunca|a veces|a menudo|casi)\b", re.I)


def restandardise(df):
    # the standard answers (gender_std, <category>_std) made again from the
    # answers as written, so a change to these rules needs no new reading of
    # the files (only the counting); an answer written for "no answer", a
    # question, or the column's own name (a header row read as data) is missing
    for cat in CAT_NAMES:
        if cat == "age":
            continue
        raw, std = cat + "_raw", ("gender_std" if cat == "gender" else cat + "_std")
        bad = [v is not None and v == v and (str(v).strip().lower() in MISSING or str(v).strip().endswith("?")
                                              or str(v).strip().lower() == str(n).strip().lower())
               for v, n in zip(df[raw].tolist(), df[cat + "_col"].tolist())]
        df.loc[bad, raw] = None
        f = gender_std if cat == "gender" else (lambda v, c=cat: value_std(c, v))
        df[std] = df[raw].map({u: f(u) for u in df[raw].dropna().unique()})
    return df


HANDS = ("right", "left", "ambidextrous")


def decode_handedness(df):
    # handedness as number codes, per file: the most frequent code is
    # right-handed (Daniel, 27 November 2026), the second left-handed and a
    # third both hands (in most samples about 10% are left-handed and a few
    # percent use both); a fourth or later code stays unknown
    coded = (df["handedness_std"] == "(a number code)").fillna(False).astype(bool)
    if not coded.any():
        return df
    key = df["preprint"].astype(str) + "|" + df["entry"].astype(str) + "|" + df["sheet"].fillna("").astype(str)
    names = ["right", "left", "ambidextrous"]
    for _, g in df[coded].groupby(key[coded]):
        order = g["handedness_raw"].value_counts().index.tolist()
        df.loc[g.index, "handedness_std"] = g["handedness_raw"].map(
            {code: (names[i] if i < len(names) else None) for i, code in enumerate(order)})
    return df


def drop_non_answers(df):
    # a column whose answers are mostly agree/disagree (a questionnaire item
    # whose name mentions religion, children, a job, ...) or numbers with
    # decimals (a score) does not describe the participants: it is emptied in
    # that file; so is a gender column whose answers are mostly not genders.
    # Returns the table and, per category, the number of files emptied.
    key = df["preprint"].astype(str) + "|" + df["entry"].astype(str) + "|" + df["sheet"].fillna("").astype(str)
    dropped = collections.Counter()
    for cat in CAT_NAMES:
        if cat == "age" or df[cat + "_raw"].isna().all():
            continue
        s = df[cat + "_raw"].dropna().astype(str)
        nums = pd.to_numeric(s.str.replace(",", ".", regex=False), errors="coerce")
        frame = pd.DataFrame({"k": key[s.index], "likert": s.str.contains(LIKERT),
                              "dec": nums.notna() & (nums % 1 != 0)})
        if cat == "gender":
            frame["unrec"] = df.loc[s.index, "gender_std"].eq("unrecognised")
        share = frame.groupby("k").mean()
        bad = share["likert"] > 0.5
        if cat not in DECIMALS:
            bad |= share["dec"] > 0.5
        if cat == "gender":
            bad |= share["unrec"] > 0.5
        bad_keys = set(share.index[bad])
        if bad_keys:
            std = "gender_std" if cat == "gender" else cat + "_std"
            df.loc[key.isin(bad_keys), [cat + "_raw", std]] = None
            dropped[cat] += len(bad_keys)
    return df, dropped


def count_all(index, args):
    parts = [os.path.join(PARTS, f) for f in os.listdir(PARTS) if f.endswith(".parquet")]
    df = pd.concat([pd.read_parquet(p) for p in parts], ignore_index=True) if parts else pd.DataFrame()
    if len(df):
        df.to_parquet(TABLE, index=False)
        df, dropped = drop_non_answers(restandardise(df))
        df = decode_handedness(df)
    else:
        dropped = collections.Counter()
    titles = {i["id"]: i.get("title") for i in index}
    done = load(DONE_FILE, {})
    age_all, gender_all = collections.Counter(), collections.Counter()
    age_shares, gender_shares = collections.defaultdict(float), collections.defaultdict(float)
    n_age_pp = n_gender_pp = n_hand_pp = 0
    hand_all, hand_shares = collections.Counter(), collections.defaultdict(float)
    values ={c: collections.Counter() for c in CAT_NAMES if c not in ("age", "gender")}
    value_pp = {c: collections.defaultdict(set) for c in values}
    has_cat = {c: [0, 0] for c in CAT_NAMES}          # preprints, people
    plat = collections.Counter()
    file_kinds = collections.Counter()
    units = collections.Counter()
    several = young_codes = 0
    papers = []
    for osf_id, d in (df.groupby("preprint", sort=False) if len(df) else []):
        people, why = preprint_people(d)
        file_kinds.update(why)
        for pl in {p for s in d["platforms"].dropna() for p in s.split(",") if p}:
            plat[pl] += 1
        for u_ in d.drop_duplicates("entry")["age_unit"].dropna():
            units[u_] += 1
        if not people:
            continue
        n = sum(p["w"] for p in people)
        several += sum(1 for p in people if p.get("several_ages"))
        ages = [(p["age_years"], p["w"]) for p in people if p["age_years"] is not None]
        if ages and sum(a * w for a, w in ages) / sum(w for _, w in ages) < CHILD_AGE \
                and not d["children_in_text"].any():
            young_codes += 1            # see CHILDREN: probably codes of age bands
            ages = []
        genders = [(p["gender_std"], p["w"]) for p in people if p["gender_std"] is not None]
        for a, w in ages:
            age_all[min(100, int(a))] += w
        for g, w in genders:
            gender_all[g] += w
        na, ng = sum(w for _, w in ages), sum(w for _, w in genders)
        if na >= MIN_SHARE_N:
            n_age_pp += 1
            for a, w in ages:
                age_shares[min(100, int(a))] += w / na
        if ng >= MIN_SHARE_N:
            n_gender_pp += 1
            for g, w in genders:
                gender_shares[g] += w / ng
        # handedness (number codes decoded by decode_handedness()), for the figure of hands
        hands = [(p["handedness_std"], p["w"]) for p in people if p.get("handedness_std") in HANDS]
        nh = sum(w for _, w in hands)
        for h, w in hands:
            hand_all[h] += w
        if nh >= MIN_SHARE_N:
            n_hand_pp += 1
            for h, w in hands:
                hand_shares[h] += w / nh
        for c in CAT_NAMES:
            key = "age_years" if c == "age" else ("gender_std" if c == "gender" else c + "_std")
            k = sum(p["w"] for p in people if p.get(key) is not None)
            if k:
                has_cat[c][0] += 1
                has_cat[c][1] += k
        for c in values:
            for p in people:
                v = p.get(c + "_std")
                if v is not None:
                    values[c][v] += p["w"]
                    value_pp[c][v].add(osf_id)
        known_g = {g: sum(w for x, w in genders if x == g) for g in ("woman", "man", "other")}
        papers.append({"id": osf_id, "t": titles.get(osf_id), "n": n, "n_age": na,
                       "age_mean": round(sum(a * w for a, w in ages) / na, 1) if na else None,
                       "age_median": weighted_median(ages) if ages else None,
                       "women": round(known_g["woman"] / sum(known_g.values()), 3) if sum(known_g.values()) else None,
                       "coded_gender": sum(w for g, w in genders if g == "coded")})

    def top_values(c, limit=TOP_VALUES):
        out = []
        for v, k in values[c].most_common():
            if k >= MIN_VALUE_N and len(value_pp[c][v]) >= 2:
                out.append([v, k, len(value_pp[c][v])])
            if limit and len(out) >= limit:
                break
        return out

    problems = collections.Counter()
    for v in done.values():
        for p in v.get("problems") or []:
            problems[re.sub(r" \(.*\)$|: .*$", "", p["reason"])] += 1
    out = {
        "updated": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "preprints_read": len(done),
        "preprints_with_people": len(papers),
        "people": sum(p["n"] for p in papers),
        "files": dict(file_kinds),
        "problems": problems.most_common(),
        "age_units": dict(units),
        # people with several ages under one ID (tested more than once); their first is counted
        "several_ages": several,
        # per category, the files whose column held no answers about participants (drop_non_answers())
        "columns_left_out": dict(dropped),
        # preprints whose ages were left out: on average under CHILD_AGE, with no children in the text
        "young_not_children": young_codes,
        "age_all": sorted([a, n] for a, n in age_all.items()),
        "age_each": {"preprints": n_age_pp, "shares": sorted([a, round(s / n_age_pp, 5)] for a, s in age_shares.items())
                     if n_age_pp else []},
        "gender_all": dict(gender_all),
        "handedness": {"all": dict(hand_all), "preprints": n_hand_pp,
                       "shares": {h: round(s / n_hand_pp, 4) for h, s in hand_shares.items()} if n_hand_pp else {}},
        "gender_each": {"preprints": n_gender_pp, "shares": {g: round(s / n_gender_pp, 4) for g, s in gender_shares.items()}
                        if n_gender_pp else {}},
        "categories": {c: {"preprints": v[0], "people": v[1]} for c, v in has_cat.items()},
        "values": {c: top_values(c) for c in values},
        # for the world map: every country of residence, and every
        # nationality, with at least MIN_VALUE_N participants in at least 2
        # preprints [name, people, preprints]
        "countries": [v for v in top_values("country", None) if not v[0].startswith("(")],
        "nationalities": [v for v in top_values("nationality", None) if not v[0].startswith("(")],
        "platforms": dict(plat),
        "papers": sorted(papers, key=lambda p: -p["n"]),
    }
    save(OUTPUT, out)
    print("%s: %d preprints, %d participants" % (OUTPUT, len(papers), out["people"]))


def check(n_values=20):
    # to look at before drawing a category: per category, the column names it
    # took (with the number of preprints) and its most frequent answers (by
    # the number of preprints, with one preprint as an example), from the
    # stored table; written to CHECK_FILE
    df, dropped = drop_non_answers(restandardise(pd.read_parquet(TABLE)))
    df = decode_handedness(df)
    out = ["Participant information in the data files, as read on %s: %d preprints" % (
        dt.date.today().isoformat(), df["preprint"].nunique()),
        "Columns emptied in a file because their answers were agree/disagree, scores with decimals, or not genders: " +
        ", ".join("%s %d" % kv for kv in sorted(dropped.items())), ""]
    for cat in CAT_NAMES:
        col = cat + "_col"
        std = "age_unit" if cat == "age" else ("gender_std" if cat == "gender" else cat + "_std")
        # a column emptied by drop_non_answers() is not listed
        d = df[df[col].notna() & (df[std].notna() if cat == "age" else df[cat + "_raw"].notna())]
        if not len(d):
            out += ["== %s: no columns found" % cat, ""]
            continue
        names = d.groupby(col)["preprint"].nunique().sort_values(ascending=False)
        out.append("== %s: %d preprints, %d column names" % (cat, d["preprint"].nunique(), len(names)))
        out.append("   columns (preprints): " + "; ".join("%s (%d)" % (c, n) for c, n in names.head(25).items()))
        v = d.groupby(std, dropna=False).agg(preprints=("preprint", "nunique"), rows=("n_rows", "size"),
                                             example=("preprint", "first")).sort_values("preprints", ascending=False)
        out.append("   %s (preprints, distinct rows, an example):" % ("units" if cat == "age" else "answers"))
        for val, r in v.head(n_values).iterrows():
            out.append("     %-42s %4d %8d  %s" % (str(val)[:42], r["preprints"], r["rows"], r["example"]))
        if cat == "gender":
            raw = d[d["gender_std"] == "unrecognised"]["gender_raw"].value_counts().head(n_values)
            out.append("   answers not recognised as a gender: " + "; ".join("%s (%d)" % (k, n) for k, n in raw.items()))
        out.append("")
    with open(CHECK_FILE, "w", encoding="utf-8") as f:
        f.write("\n".join(out) + "\n")
    print("written: %s" % CHECK_FILE)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data-dir", default="data")
    ap.add_argument("--count-only", action="store_true")
    ap.add_argument("--check", action="store_true", help="only write the list to check (CHECK_FILE)")
    ap.add_argument("--redo", nargs="*", default=[])
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()
    index = load(os.path.join(args.data_dir, "index.json"), {"papers": []}).get("papers", [])
    os.makedirs(OUT_DIR, exist_ok=True)
    if args.check:
        check()
        return
    if not args.count_only:
        read_all(args, index, secret_key())
    count_all(index, args)


if __name__ == "__main__":
    main()
