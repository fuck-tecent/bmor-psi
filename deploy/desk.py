import hashlib
import hmac
import ipaddress
import json
import re
import secrets
import sqlite3
import time
from collections import Counter
from contextlib import closing, contextmanager, nullcontext
from pathlib import Path
from urllib.parse import urlencode

if __package__:
    from . import reductions
else:
    import reductions

NO_RESEARCH_DEADLINE = 253402300799  # Keep the existing integer lease protocol.
SUBMISSION_SECONDS = 12 * 60 * 60
CHECK_SECONDS = 3 * 60 * 60
NETWORK_ACTIVE_LIMIT = 3
NETWORK_HOURLY_LIMIT = 12
FLEET_ACTIVE_LIMIT = 128
QUEUE_BATCH = 16
QUEUE_RETRY_SECONDS = 15 * 60
HANDLE = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*", re.ASCII)
HEAD = re.compile(r"[0-9a-f]{40}", re.ASCII)
TOKEN = re.compile(r"Bearer ([A-Za-z0-9_-]{43})", re.ASCII)
RELEASE_REASONS = {
    "abandoned",
    "does_not_elaborate",
    "exhausted",
    "hypothesis_too_weak",
    "missing_lemma",
    "not_a_fit",
    "other",
    "out_of_time",
    "statement_seems_false",
    "superseded",
}


HARNESS_NAMES = (
    'codex',
    'claude-code',
    'cursor',
    'gemini-cli',
    'opencode',
    'kimi-code',
    'minimax-code',
    'zcode',
    'qwen-code',
    'qoder',
    'qoder-cn',
    'lingma',
    'trae',
    'codebuddy',
    'comate',
    'codegeex',
    'iflycode',
    'github-copilot',
    'github-copilot-cli',
    'windsurf',
    'cline',
    'roo-code',
    'kilo-code',
    'continue',
    'aider',
    'goose',
    'openhands',
    'kiro',
    'amazon-q',
    'augment-code',
    'auggie',
    'devin',
    'devin-desktop',
    'jetbrains-ai',
    'jetbrains-air',
    'junie',
    'zed',
    'warp',
    'tabnine',
    'replit-agent',
    'factory-droid',
    'mistral-vibe',
    'pi',
    'antigravity',
    'hermes-agent',
    'swe-agent',
    'mini-swe-agent',
    'open-interpreter',
    'other',
    'unknown',
)
# Historical PRs recorded as 'other' before the named tools were supported.
# Each PR body explicitly names the harness and matches the accepted author and head.
# Keys pin the exact GitHub pull request revision. Original submissions stay intact.
HISTORICAL_HARNESSES = {
    (2763, "06a31a385d4ce3d6677606f62334d6ca70b8eb7a"): "minimax-code",
    (2766, "42154c1cfd2e844bab35a1b5e21e3a5ab642f036"): "minimax-code",
    (2768, "13ac95d36a625cd474f770557f066fcea7ae916f"): "minimax-code",
    (2773, "94d053c1807ffaf2aa58ec15cb663338e938fd5e"): "minimax-code",
    (2776, "982d2d516918ec2c075a14c5f78ccf462743c2ac"): "minimax-code",
    (2778, "9abae654d61f2a6de720e4f6231fd42a6669a714"): "minimax-code",
    (2780, "313f21f625601edc215192c7b00e9d9ceef3d2ba"): "minimax-code",
    (2783, "70f8d242604b07d820b533b9bea5123de873adcf"): "minimax-code",
    (2799, "7022b77f3bf649058e02fd1e4f6b9112e1917306"): "minimax-code",
    (2835, "fc9c02769672648b2ee1115b2ddb551c941aead1"): "minimax-code",
    (2836, "944cb0beda66ff9b14a94181a2bd60ce79ce1647"): "minimax-code",
    (2858, "60392c42862cdbc5f4e314298c39c115a844abef"): "minimax-code",
    (2860, "aee9c9b5b13ea31dc79acc4e3e2056ebfbddd43a"): "minimax-code",
    (2871, "b49f619118aeb316cbd726aaac198947408cc852"): "minimax-code",
    (2877, "4594d65429fa0aeb0329f9fe8d7aeffd3621231e"): "minimax-code",
    (2880, "63a61122b8fd3d6d1ae425fce6a9f70062156131"): "minimax-code",
    (2881, "463d87ccab03793c55b467b37ffe8ec2c39025fe"): "minimax-code",
    (2882, "c22107e8b1dd3183484a4f20dd24e6d23ee70ba4"): "minimax-code",
    (2883, "f96c6b2dffd3f9085f933b6842a6a243e8d31683"): "minimax-code",
    (2888, "2e5f8557a0981c4302e2d47e43b351eb37f4c455"): "minimax-code",
    (2890, "69f2f7eb5d1275177e4c74f2193067743560488b"): "minimax-code",
    (2893, "0fb310ffc0c874a8967b070c901e3ae81b7f8944"): "minimax-code",
    (2895, "ea0bfdf232d0fd18f84c42827e31d32954b2629c"): "minimax-code",
    (2896, "06fc95e227452f7b3a01a63689542e149aa3b082"): "minimax-code",
    (2897, "2a2ac784a81fb63fed096c1f2ff9f26f4ba7799c"): "minimax-code",
    (2906, "efd8007b4aa003016b9ee0460896f5aecdb48416"): "minimax-code",
    (2911, "91f9c9c65d888662d27bec2fe0999e776c202940"): "minimax-code",
    (2912, "70a0b694eab17efbbff87fa410b3342c03a96e60"): "minimax-code",
    (2914, "384851f07a57d4ce491e58f3d7bd73c690159088"): "minimax-code",
    (2919, "8f26e0d6ed563321e32969bf6c05149c5cdd0cac"): "minimax-code",
    (2921, "cd75ade563c91321897297c7e17454576c6319b8"): "minimax-code",
    (2925, "608042182c74e42634684677427d160bf5bf37d9"): "minimax-code",
    (2926, "dea3fa2e5b718969c52b98ff4e95c795e884668c"): "minimax-code",
    (2928, "2b1c0500a92b1f9d6e99c019fa849efbb2f745ed"): "minimax-code",
    (2932, "3b6c04e88260a26b7ad32378710c75a21b2a7559"): "minimax-code",
    (2933, "3459736d5abe9c753d79c8bdd93c104e3aceb252"): "minimax-code",
    (2935, "316cc80773aabef66790e00fd376a39d984d5576"): "minimax-code",
    (2936, "e3d3d1f784d7f7a664e1e5b86494f6d5acfdf18e"): "minimax-code",
    (2938, "3630aceea832659fb22c53c74f1c42a7d91d598d"): "minimax-code",
    (2944, "e8d741a9b34c0bffeb515d781e2c12f4da77d43a"): "minimax-code",
    (2945, "8fa7e6bcfe800d5fd322586b58f8661c4554866b"): "minimax-code",
    (2950, "1edd664c6ebf3ff350aa6d284576dc038940df0a"): "minimax-code",
    (2951, "73bf1a105a3ed334319831909577dd3d18dc5679"): "minimax-code",
    (2954, "e5a6d11982d500c416165c4ee223a7a2346ce500"): "minimax-code",
    (2956, "035343d8d8e3df29162213eb701e58ec370efbe5"): "minimax-code",
    (2960, "6bd596b21e237b22cb1696aef95c505d08f305db"): "minimax-code",
    (2961, "e24cad6088199ea9daca4fe0b8ec32723b090adf"): "minimax-code",
    (2963, "cce6782e08b84ba8fe5dc4975fc6a99bbe4a97ae"): "minimax-code",
    (2967, "b58709993e65337e626dc2bdcd76b8cd1dc7e5fe"): "minimax-code",
    (3072, "cc2ba8d88731cf39ce366c092bb548d695d586c9"): "minimax-code",
    (3077, "d1db7ee09b3608dea145fac5f2f5bc0fc423c6e1"): "minimax-code",
    (3079, "4257dc938b858aacef30f0895ed781458acf3544"): "minimax-code",
    (3097, "118d232b423edd72fb7ee0377887304ad8f6c97b"): "minimax-code",
    (3120, "1067979f721941af7326ee9292ecd850f744c550"): "minimax-code",
    (3122, "0f9d1ed6ced6ba263976d3942b612c8c8db7bff6"): "minimax-code",
    (3123, "5dcc5a4922045ce3d9d73d24f5fb7b2bb681bc4a"): "minimax-code",
    (3124, "99020bf57fb80332fceb70bec7f5bb7b49d3dc3d"): "minimax-code",
    (3125, "4515a5c273aec0327490e8615a4c0c03ac91aa92"): "minimax-code",
    (3126, "41ec6d466d8c3a7980c4cf9237242703b6e463c2"): "minimax-code",
    (3127, "b0f5f1d12004f304c3d4c6a5f52541158b675a17"): "minimax-code",
    (3128, "4b4d99a97f364fa608bd232ba669a1805301a226"): "minimax-code",
    (3129, "56b0946f06d4d1b420097939b88b186354a4b3df"): "minimax-code",
    (3130, "c40e3e73261478ae9ff0172742e071f1dd420ba9"): "minimax-code",
    (3131, "2a5541b014dd741ddbae6c1581f43c2ab1cf69e3"): "minimax-code",
    (3132, "86845220817832545ccdd1da46e7152cc9214f5a"): "minimax-code",
    (3136, "66e9889f33e02532135ca58f20ee921b0b6de829"): "minimax-code",
    (3138, "f36ac7ab85e2b09933db0df16da2d12f4bf08b6d"): "minimax-code",
    (3139, "9c2abb040dcf37d9413d780d6f28a70f83235936"): "minimax-code",
    (3141, "d9e27e0c465bfb9d7de02c2aa6cbdb0522ddeaee"): "minimax-code",
    (3142, "ac91cc7e5554a6691edc716deb010e9aa2c7c80a"): "minimax-code",
    (3143, "1af1ff9b2ea324cdc08dd70e4735327f48fd8496"): "minimax-code",
    (3144, "edc910a4ee5a4911992d6eb1db7892769a197279"): "minimax-code",
    (3234, "9e0dccc0f0ce803d914965989fc7251e3593fbf1"): "minimax-code",
    (3238, "b5e96b222d11b1425e56d9f05fff2e9491357845"): "minimax-code",
    (3240, "309a3144e38f881f60cfa699d9c05a303cccf813"): "minimax-code",
    (3246, "d0c566b24f490ad7044baef8bb2e6ae6a6ae4068"): "minimax-code",
    (3254, "98749f4edc7f13fcdde8116ccbe305780f9236a3"): "minimax-code",
    (3270, "0bfac4c83c42cd0c55fbd15774b7a554959e497c"): "minimax-code",
    (3282, "530a1910f3d006f47737d6c55c461d1a2ad9dd34"): "minimax-code",
    (3286, "0010156bdfb5f2d989d24f6c9687b39828c20566"): "minimax-code",
    (3287, "f3924ca60e6094d5ff9bfae553a40080014213e8"): "minimax-code",
    (3288, "92b3e641fff3b1c3902c525b4dbf3e73023e085d"): "minimax-code",
    (3294, "e3e7fbe3a0c28c4e0d661e9d216d1a246d211929"): "minimax-code",
    (3297, "eeda31d0d421b58f7d060e93e692a4f9a5e0f020"): "minimax-code",
    (3298, "aa84f7ea4ab781f21f396ff3340320388e99abe6"): "minimax-code",
    (3299, "b6300ff9dd9aeec902cb3bd8296d819bcb770729"): "minimax-code",
    (3300, "376968e61b50691100f64aa857a1731124fdad13"): "minimax-code",
    (3301, "d4fde4853d3c2f21c7f3a2feb2dabcc86fbb87a2"): "minimax-code",
    (3302, "c03798eaaaf2ae0fa8fe2cbe341d9765a6b7ab49"): "minimax-code",
    (3303, "fb76767382f0f48c23fb34ec2ed838944f389d62"): "minimax-code",
    (3304, "47585ef5c48adbb282b698d38a1f6ee44e7b47f7"): "minimax-code",
    (3305, "34f384434e9cdcdfefd635aa579b571878704a88"): "minimax-code",
    (3306, "6476229736c66e42a5434ccfe8e76af629ae33b0"): "minimax-code",
    (3307, "52de68effdbd368c486cffdf8fa465fa5a094c48"): "minimax-code",
    (3309, "9849d4c325a4465cd28c932875eb0104a03297bf"): "minimax-code",
    (3311, "18d8ff8c74b6ea655b7a14e91f3a34e67778f11a"): "minimax-code",
    (3312, "234e5e1fa28582697856592995d446d13c241b07"): "minimax-code",
    (3313, "3d4b08ab0732343a4c2aad8a727243e66fe68c85"): "minimax-code",
    (3314, "cfaade4d262e3d8d97246d02fdb6259cecab950c"): "minimax-code",
    (3315, "f6bd728e34807974c8ca65eb6b4387b5d8a27a16"): "minimax-code",
    (3317, "6c7b060b330e9e48926341a1e1a5f725910349c1"): "minimax-code",
    (3318, "f2374d2713c9824519b598f8faaa76914e9a49f2"): "minimax-code",
    (3320, "6e6a766ce545dc2a6dd4a31ef88ab0e4ba15b938"): "minimax-code",
    (3321, "d6a99bb8abd251067076daeeea81b5ed03697183"): "minimax-code",
    (3322, "943ed2a92017439f057d495002aa1f7681527aa2"): "minimax-code",
    (3323, "2e61e00adc5fdc595de98c8a29b36867989dc28d"): "minimax-code",
    (3324, "c0798ef7d7868e194ec81d373932ca642d2f9916"): "minimax-code",
    (3325, "789160221441eac6def56ada4dd01bfab3723a66"): "minimax-code",
    (3327, "3174b498e251169b4e5de9615d08b52373ab61f0"): "minimax-code",
    (3329, "b5e755ecb46ebecc60620a6624fe46a1ca42512c"): "minimax-code",
    (3331, "0c1d9b43b77a5b6d6104c553401b00489e3845f7"): "minimax-code",
    (3332, "def7f43dac65436447c0ab9644561b9eeeff38f7"): "minimax-code",
    (3334, "6edeb762961c55a6e5050c53719932a687babe89"): "minimax-code",
    (3335, "7bfe0c329a6c79f15f0d7d400383e14ab4f5e4a1"): "minimax-code",
    (3336, "ee1ecac40fb2f88b4b866a6cf22c544abd17dd0a"): "minimax-code",
    (3337, "ab39635f1d9ac7e16e2b3481ffbb71c5617872bf"): "minimax-code",
    (3382, "cb5d44ba62e43281a4a5cee2018a9df14739ef76"): "minimax-code",
    (3388, "930dd956aa7782bd745ed6064f9857d600393cc6"): "minimax-code",
    (3394, "6ff12f601435848b3fb527bd73f1d66044c3241b"): "minimax-code",
    (3395, "71f51b094662d98d2b1bfec84d92f40197805c4f"): "minimax-code",
    (3397, "07119a2a2f7585a3a33d4e39eab0f62c14340f4f"): "minimax-code",
    (3399, "1ce9efd4ba654ce4e9cd280f9a9a347b6c59740d"): "minimax-code",
    (3428, "308d37d60d04721a35141e24b240d496ba754f3a"): "minimax-code",
    (3432, "03c5d16bc7f832edac39ecf2bf15fc3708b2a3f7"): "minimax-code",
    (3474, "22a2a339dab23b9a9dc5ff0945b16fe661663580"): "minimax-code",
    (3475, "ae7d409fb432901ab01facdc431a859ec4353748"): "minimax-code",
    (3478, "642ad63d56c4fade79f556ea8b80e70cffb0a41c"): "minimax-code",
    (3481, "498844b1a55134f928d214e7b17996ad85130052"): "minimax-code",
    (3484, "1b4c32a259bd1ccdb81b1137de024d76f6333d29"): "minimax-code",
    (3485, "0fb442eca59cc99230a40dd6f19129f4bc0d0c73"): "minimax-code",
    (3486, "8f9f0dd9947f7dff8cbf38b75528d70f7657f230"): "minimax-code",
    (3500, "2edd3fef7599fe16015e577f2630dbe7e00f3db6"): "minimax-code",
    (3503, "1c0c78e4bb8d433c3a4b9a0632eda5d1454460c2"): "minimax-code",
    (3506, "cf85124e0adf0b6a7be81f6dd492bc34398d9d58"): "minimax-code",
    (3508, "3e17d254b46f78d69708c932d29052e3c7c3b351"): "minimax-code",
    (3509, "d90e9a54c25c53eb8d46e76744c8948e7d9fdb1c"): "minimax-code",
    (3513, "e6bc6bffdcf110f00ad536336b2c625b647244d1"): "minimax-code",
    (3518, "401703bb9b5df49b68f403d52d7d2be00d0c2840"): "minimax-code",
    (3519, "a91564cbf195c2769e93a1def3e5b5581f6762f6"): "minimax-code",
    (3523, "146412c8e0b96d5444b1749b5a37215917d4a5e9"): "minimax-code",
    (3525, "533aa14b2eda8d3cb21f46c780a799c68a3df586"): "minimax-code",
    (3526, "18aa6d2582c892b8185875364e6658bfb28f1b61"): "minimax-code",
    (3533, "0fc883ca22e4c8a40e458acfefdf7e86ba02c284"): "minimax-code",
    (3534, "e3f5daf152498d22ddde7c4d8f992603b4a1ad87"): "minimax-code",
    (3535, "389244edd2a39fc0f8c6b4748893e39196754c8e"): "minimax-code",
    (3538, "3033be232c02c42b2c32d88f73b72dda236dc104"): "minimax-code",
    (3539, "fa30f60eb8475f64d98213fe93f44375e8dec7e0"): "minimax-code",
    (3542, "8d7f05fd4b05cbf56815369b6621588a3dd3fec2"): "minimax-code",
    (3543, "e748b1c2e0f325d731e47545269b1aa0ab21a767"): "minimax-code",
    (3545, "5409d43567780cd2d8c6be8220fd582d36fae036"): "minimax-code",
    (3547, "8869b13f46b59847a63d245674122f4bf16b163a"): "minimax-code",
    (3549, "2eab8a2be7c9e207a5324bb1d0f76a869c2c782e"): "minimax-code",
    (3550, "ac082213e5d81b108bf9f4298b85530082220c26"): "minimax-code",
    (3551, "de9ee7c7fc4172aef5930d7956719715b8c04b56"): "minimax-code",
    (3552, "697bf95ce462b54218dea186a5ab3276ccf344fa"): "minimax-code",
    (3553, "73bbf90059c2d6a917d678f738003d677130e24e"): "minimax-code",
    (3554, "436dac03daef438f155ec10f0c7643570bb30c8c"): "minimax-code",
    (3555, "a1837d819764fd76135c3f74b064f509211173fe"): "minimax-code",
    (3556, "f0f8e1a39c1d746745870a1fb90eb06abe989095"): "minimax-code",
    (3557, "c5e414248ec5a84769d36b017a5c19fa284acee2"): "minimax-code",
    (3560, "6608ee417f4f03189767e5f3b579b8e2fea73ade"): "minimax-code",
    (3561, "a580206b1e2f3fdd9afa165366d71f76a3737cca"): "minimax-code",
    (3563, "a67495f692602d0717e6059db4da9887dd354554"): "minimax-code",
    (3564, "2ea34ceb47053e6df4f27deac26e84e19de38eff"): "minimax-code",
    (3565, "4a31b3c6de104d65142a46f511c54555620c75d7"): "minimax-code",
    (3566, "e7569b2942a4910baa46d622dafcbb83c28309d1"): "minimax-code",
    (3567, "e0f3a15bad9ef3def56b3e8850eee5bdfcb9b794"): "minimax-code",
    (3570, "e20965212edaef3569d5bebbc4adf32032a92a66"): "minimax-code",
    (3571, "e6e6dcad726db274e620d5103030523a41e12e76"): "minimax-code",
    (3572, "016f13c3179b71edf47058d94d10090566910c97"): "minimax-code",
    (3573, "dfe6615ac881b11d2e9f845020ff74f6cc6eb155"): "minimax-code",
    (3574, "4ba32edca86ef2015cd20e925321cdf2e6272834"): "minimax-code",
    (3575, "e9863766ea67cfb1e009326f00ba578cfacd8234"): "minimax-code",
    (3576, "e6f354e570139e5b6c9af1d61a822d179a9ff279"): "minimax-code",
    (3578, "da54e0d8de15dbc8416d1d8382bd1fa5fc8d4b71"): "minimax-code",
    (3583, "5be7487dab6d95e6fa2cf78aaf4c3b4e40549bbf"): "minimax-code",
    (3584, "be5a9d62fe5ffb037fbbef9c424848f20375ab90"): "minimax-code",
    (3585, "54266a47196f88656ebdddda7ee0ae1e344af561"): "minimax-code",
    (3588, "f45a2f25c64c0b58dcda6d3d1a4d949bfc646e7d"): "minimax-code",
    (3589, "3d1ce3e777dec5f31e76cf15c7dfb043b71fe249"): "minimax-code",
    (3592, "53147ed364235c071baff910b9deadbd41fccff8"): "minimax-code",
    (3593, "35d5678add2499f88face5563b251e82a3d6f286"): "minimax-code",
    (3594, "5f831d3649e1b4f9e79e64dc336e4ee10951c8fa"): "minimax-code",
    (3600, "29a85e9c23a2243976bc2f26ccf767b97705f00a"): "minimax-code",
    (3606, "e40354e1b759b688e7d5e1b4d5046444d6de74c3"): "minimax-code",
    (3612, "2366f2b0660bcc65d4dfe2c0c3a25eba62498095"): "minimax-code",
    (3615, "919c3e44522724be404d6ddb33022e34e996b687"): "minimax-code",
    (3616, "afc8194f34dec49d96ac9338aa3acfdc388ba540"): "minimax-code",
    (3626, "dd80d09448e9ede6a255f1fc66cfea49cf50909b"): "minimax-code",
    (3636, "744c43d8049f2caadde131e524b6d17532b9cdb4"): "minimax-code",
    (3646, "420b4c57dd820f58bdd9e96bd0d4b52adf0c2ce3"): "minimax-code",
    (3652, "5638809aa61e91cc407488f057a9731980af2f45"): "minimax-code",
    (3653, "72c2b191ca260e29bb369e6c00b18c98fae3927f"): "minimax-code",
    (2359, "d5a3e1dd50f23646d6a18fd453bc1c58927dd151"): "zcode",
    (2361, "190bc320138d37ae58b6c14b7f292b4c80d4cff0"): "zcode",
    (2379, "13f56a552dcbe5f50dbc5fbccc61188713a713be"): "zcode",
    (2425, "a85bc3bb1afcdb75d3584ae40efb8dc541500754"): "zcode",
}

AGENT_LABEL = re.compile(r"[a-zA-Z0-9][a-zA-Z0-9 ._:/+\-]{0,95}", re.ASCII)
UUID_PREFIX = re.compile(
    r"^(?:[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}|[0-9a-f]{16,})/"
)
CHANNEL_SUFFIX = re.compile(
    r":(?:free|beta|extended|thinking|nitro|floor|online|exacto|[0-9]+)$"
)
BEDROCK_REGION_PREFIX = re.compile(r"^(?:us|eu|ap|apac|global)\.")
# Cloud hosts, routers, proxies and local runtimes — not model authors.
GATEWAY_PREFIXES = frozenset({
    "openrouter", "aws", "amazon-bedrock", "bedrock", "vertex", "vertex-ai", "vertex_ai",
    "gcp", "azure", "azure-openai", "together", "togetherai", "together-ai",
    "fireworks", "fireworks-ai", "siliconflow", "siliconcloud", "volcengine", "volces",
    "ark", "bailian", "dashscope", "aliyun", "litellm", "ollama", "vllm", "sglang",
    "lmstudio", "deepinfra", "novita", "groq", "cerebras", "sambanova", "chutes",
    "parasail", "nebius", "hyperbolic", "cloudflare", "workers-ai", "replicate",
    "lepton", "baseten", "modal", "anyscale", "github", "github-models", "copilot",
    "poe", "api", "proxy", "gateway", "relay", "oneapi", "newapi",
})
# Model hubs that host both their own models and third-party open-weights models.
HUB_PREFIXES = frozenset({"huggingface", "hugging-face"})

# Only recognize this explicit family of aliases. Do not strip arbitrary model suffixes:
# dates, preview names, fine-tunes and other providers may encode distinct models there.
GPT_VARIANT = re.compile(
    r"(?:openai[/:])?(?:gpt[ _-]?)?(\d+(?:\.\d+)+)[ _-]+"
    r"(astra|sol|terra|luna)(?:[ _-]*(?:none|minimal|low|medium|high|xhigh|max|ultra))?"
)


# Explicit, auditable alias mappings loaded from deploy/model-aliases.json (read-time
# rankings only; stored submission provenance and verification records stay untouched).
MODEL_ALIASES_FILE = Path(__file__).resolve().with_name("model-aliases.json")
_DEFAULT_MODEL_ALIASES = {
    "model_aliases": {
        "big fat fish v4.1-flash": "deepseek-v4.1-flash",
        "gpt-6 astra pro": "gpt-6-astra-pro",
        "minimax m78": "minimax-m78",
        "gemini-neon": "gemini-4-neon",
        "gemini 4": "gemini-4",
        "gemini-4-carbon-high": "gemini-4-carbon",
        "gemini 4 hydrogen": "gemini-4-hydrogen",
        "gemini-4-hydrogen-high": "gemini-4-hydrogen",
        "k3.1-pro": "kimi-k3.1-pro",
    },
    "provider_aliases": {
        "hy4std": "Tencent",
        "hy4-flash-free": "Tencent",
    },
}


def _load_model_aliases(path=MODEL_ALIASES_FILE):
    raw = json.loads(path.read_text(encoding="utf-8")) if path.is_file() else _DEFAULT_MODEL_ALIASES
    model_aliases = {
        " ".join(k.lower().split()): " ".join(v.lower().split())
        for k, v in raw.get("model_aliases", {}).items()
    }
    provider_aliases = {
        " ".join(k.lower().split()): v.strip()
        for k, v in raw.get("provider_aliases", {}).items()
    }
    return model_aliases, provider_aliases


MODEL_NAME_ALIASES, MODEL_EXACT_ALIASES = _load_model_aliases()


def strip_uuid_prefix(label):
    while True:
        stripped = UUID_PREFIX.sub("", label, count=1)
        if stripped == label or not stripped:
            return label
        label = stripped


def model_ranking_name(value):
    """Group known spelling/effort/nickname aliases and strip opaque UUID tenant prefixes."""
    label = strip_uuid_prefix(" ".join(value.lower().split()))
    if label in MODEL_NAME_ALIASES:
        return MODEL_NAME_ALIASES[label]
    match = GPT_VARIANT.fullmatch(label)
    return f"gpt-{match[1]}-{match[2]}" if match else label


# Single source of truth for model developers, prefix/family rules and brand icons.
# Model authors and model-family labels, not API hosts or coding tools.
# Reference: https://openrouter.ai/models and https://models.dev/
MODEL_REGISTRY = {
    "OpenAI": {
        "icon": "openai",
        "orgs": ("openai",),
        "families": (r"gpt", r"chatgpt", r"o[134](?=$|[._:-]|-mini|-pro|-preview)"),
    },
    "Anthropic": {
        "icon": "claude",
        "orgs": ("anthropic",),
        "families": (r"claude",),
    },
    "Google": {
        "icon": "google",
        "orgs": ("google",),
        "families": (r"gemini", r"gemma", r"palm"),
        "family_icons": ((r"gemini", "gemini"), (r"gemma", "gemma")),
    },
    "MiniMax": {
        "icon": "minimax",
        "orgs": ("minimax", "minimaxai"),
        "families": (r"minimax", r"abab"),
    },
    "DeepSeek": {
        "icon": "deepseek",
        "orgs": ("deepseek", "deepseek-ai"),
        "families": (r"deepseek",),
    },
    "Alibaba": {
        "icon": "alibaba",
        "orgs": ("alibaba", "qwen", "tongyi"),
        "families": (r"qwen", r"qwq", r"qvq", r"tongyi"),
        "family_icons": ((r"qwen|qwq|qvq|tongyi", "qwen"),),
    },
    "Moonshot AI": {
        "icon": "moonshot",
        "orgs": ("moonshot", "moonshotai"),
        "families": (r"kimi", r"moonshot"),
        "family_icons": ((r"kimi", "kimi"),),
    },
    "Meta": {
        "icon": "meta",
        "orgs": ("meta", "meta-llama"),
        "families": (r"llama",),
    },
    "Mistral AI": {
        "icon": "mistral",
        "orgs": ("mistral", "mistralai"),
        "families": (r"mistral", r"mixtral", r"codestral", r"devstral", r"magistral", r"ministral", r"pixtral", r"voxtral"),
    },
    "xAI": {
        "icon": "xai",
        "orgs": ("xai", "x-ai"),
        "families": (r"grok",),
        "family_icons": ((r"grok", "grok"),),
    },
    "Z.ai": {
        "icon": "zhipu",
        "orgs": ("zai", "z-ai", "zhipu", "zhipuai", "thudm"),
        "families": (r"glm", r"chatglm"),
    },
    "ByteDance": {
        "icon": "bytedance",
        "orgs": ("bytedance", "bytedance-seed"),
        "families": (r"doubao", r"seed(?=[ -]?[0-9]|-oss|-coder|-pro|-thinking)"),
        "family_icons": ((r"doubao|seed", "doubao"),),
    },
    "Baidu": {
        "icon": "baidu",
        "orgs": ("baidu",),
        "families": (r"ernie", r"wenxin"),
        "family_icons": ((r"ernie|wenxin", "wenxin"),),
    },
    "Tencent": {
        "icon": "tencent",
        "orgs": ("tencent",),
        "families": (r"hunyuan", r"hy(?=[0-9])"),
        "family_icons": ((r"hunyuan|hy(?=[0-9])", "hunyuan"),),
    },
    "StepFun": {
        "icon": "stepfun",
        "orgs": ("stepfun", "step-fun"),
        "families": (r"step(?=[ -]?[0-9])",),
    },
    "Microsoft": {
        "icon": "microsoft",
        "orgs": ("microsoft",),
        "families": (r"phi(?=$|[0-9 ._-])", r"mai(?=[ -]?[0-9])"),
    },
    "NVIDIA": {
        "icon": "nvidia",
        "orgs": ("nvidia",),
        "families": (r"nemotron",),
    },
    "Amazon": {
        "icon": "amazon",
        "orgs": ("amazon",),
        "families": (r"amazon-nova", r"nova(?=-?(?:micro|lite|pro|premier|sonic|reel|canvas|[0-9]))"),
        "family_icons": ((r"amazon-nova|nova", "nova"),),
    },
    "IBM": {
        "icon": "ibm",
        "orgs": ("ibm", "ibm-granite"),
        "families": (r"granite",),
    },
    "Cohere": {
        "icon": "cohere",
        "orgs": ("cohere",),
        "families": (r"command-r", r"command-a", r"aya-expanse"),
    },
    "AI21 Labs": {
        "icon": "ai21",
        "orgs": ("ai21", "ai21labs"),
        "families": (r"jamba",),
    },
    "Perplexity": {
        "icon": "perplexity",
        "orgs": ("perplexity",),
        "families": (r"sonar",),
    },
    "01.AI": {
        "icon": "zeroone",
        "orgs": ("01-ai", "01.ai"),
        "families": (r"yi(?=-[0-9])",),
    },
    "Xiaomi": {
        "icon": "xiaomi",
        "orgs": ("xiaomi",),
        "families": (r"mimo",),
    },
    "InclusionAI": {
        "icon": "ling",
        "orgs": ("inclusionai", "inclusion-ai"),
        "families": (r"ling(?=[ -]?[0-9])", r"ring(?=[ -]?[0-9])"),
    },
    "Meituan": {
        "icon": "longcat",
        "orgs": ("meituan",),
        "families": (r"longcat", r"long-cat"),
    },
    "Nex AGI": {
        "icon": "nex-agi",
        "orgs": ("nex-agi", "nexagi"),
        "families": (r"nex-n(?=[0-9])",),
    },
    "Allen Institute for AI": {
        "icon": None,
        "orgs": ("allenai", "ai2"),
        "families": (r"olmo", r"molmo", r"tulu"),
    },
    "Nous Research": {
        "icon": "nous",
        "orgs": ("nousresearch", "nous-research"),
        "families": (r"hermes(?=[ -]?[0-9])",),
    },
    "Hugging Face": {
        "icon": "huggingface",
        "orgs": ("huggingface", "hugging-face", "huggingfaceh4"),
        "families": (r"smollm",),
    },
    "Naver": {
        "icon": None,
        "orgs": ("naver",),
        "families": (r"hyperclova",),
    },
    "LG AI Research": {
        "icon": "lg",
        "orgs": ("lgairesearch", "lg-ai-research"),
        "families": (r"exaone",),
    },
    "NCSOFT": {
        "icon": None,
        "orgs": ("ncsoft",),
        "families": (r"varco",),
    },
    "Writer": {
        "icon": None,
        "orgs": ("writer",),
        "families": (r"palmyra",),
    },
}

# Semantic SVG sprite icon keys (`deploy/agent-icons.svg#brand-<key>`) for coding harnesses.
HARNESS_ICONS = {
    "codex": "codex",
    "claude-code": "claude-code",
    "cursor": "cursor",
    "gemini-cli": "gemini-cli",
    "opencode": "opencode",
    "kimi-code": "kimi",
    "minimax-code": "minimax",
    "zcode": "zcode",
    "qwen-code": "qwen",
    "qoder": "qoder",
    "qoder-cn": "qoder",
    "lingma": "alibaba",
    "trae": "trae",
    "codebuddy": "codebuddy",
    "comate": "baidu",
    "codegeex": "codegeex",
    "iflycode": "iflytek",
    "github-copilot": "github-copilot",
    "github-copilot-cli": "github-copilot",
    "windsurf": "windsurf",
    "cline": "cline",
    "roo-code": "roo-code",
    "kilo-code": "kilo-code",
    "goose": "goose",
    "openhands": "openhands",
    "kiro": "kiro",
    "amazon-q": "amazon",
    "devin": "devin",
    "devin-desktop": "devin",
    "junie": "junie",
    "replit-agent": "replit",
    "mistral-vibe": "mistral",
    "antigravity": "antigravity",
    "hermes-agent": "nous",
    "other": "tool-other",
}

# Canonical model catalog snapshot for client discovery (`GET /api/models`,
# `python tools/goldbach.py models`) and Tier-2 classification.
# Never put raw aliases from deploy/model-aliases.json here.
# Synced offline via `python tools/sync_models.py sync`.
# BEGIN MODEL_CATALOG
MODEL_CATALOG = {
    "gpt-6.2-astra": "OpenAI",
    "gpt-6.2-sol": "OpenAI",
    "gpt-6.2-terra": "OpenAI",
    "gpt-6.2-luna": "OpenAI",
    "gpt-6.2": "OpenAI",
    "gpt-6.1-sol": "OpenAI",
    "gpt-6.1-terra": "OpenAI",
    "gpt-6-astra-pro": "OpenAI",
    "gpt-6-luna": "OpenAI",
    "gpt-6": "OpenAI",
    "gpt-5.6-sol": "OpenAI",
    "gpt-5.4": "OpenAI",
    "gpt-5.4-mini": "OpenAI",
    "gpt-5.4-pro": "OpenAI",
    "gpt-5.3-codex": "OpenAI",
    "gpt-5.2": "OpenAI",
    "gpt-5": "OpenAI",
    "gpt-4.1": "OpenAI",
    "gpt-4o": "OpenAI",
    "o3": "OpenAI",
    "o3-pro": "OpenAI",
    "o4-mini": "OpenAI",
    "claude-opus-5-5": "Anthropic",
    "claude-fable-5-2": "Anthropic",
    "claude-opus-4.6": "Anthropic",
    "claude-opus-4.5": "Anthropic",
    "claude-opus-4.1": "Anthropic",
    "claude-opus-4": "Anthropic",
    "claude-sonnet-4.6": "Anthropic",
    "claude-sonnet-4.5": "Anthropic",
    "claude-sonnet-4": "Anthropic",
    "claude-haiku-4.5": "Anthropic",
    "claude-3.7-sonnet": "Anthropic",
    "gemini-4-neon": "Google",
    "gemini-4-carbon": "Google",
    "gemini-4-hydrogen": "Google",
    "gemini-4": "Google",
    "gemini-3.1-pro": "Google",
    "gemini-3-pro": "Google",
    "gemini-3-flash": "Google",
    "gemini-2.5-pro": "Google",
    "gemini-2.5-flash": "Google",
    "gemma-3-27b-it": "Google",
    "minimax-m78": "MiniMax",
    "minimax-m3.1-flash": "MiniMax",
    "minimax-m2.5": "MiniMax",
    "minimax-m2.1": "MiniMax",
    "minimax-m2": "MiniMax",
    "minimax-m1": "MiniMax",
    "deepseek-v4.1-flash": "DeepSeek",
    "deepseek-v4-pro": "DeepSeek",
    "deepseek-flash": "DeepSeek",
    "deepseek-v4": "DeepSeek",
    "deepseek-v3.2": "DeepSeek",
    "deepseek-v3.1": "DeepSeek",
    "deepseek-v3": "DeepSeek",
    "deepseek-r1": "DeepSeek",
    "qwen3.7-plus": "Alibaba",
    "qwen3.5-plus": "Alibaba",
    "qwen3-max": "Alibaba",
    "qwen3-coder": "Alibaba",
    "qwen3-235b-a22b": "Alibaba",
    "qwq-32b": "Alibaba",
    "kimi-k3.1-pro": "Moonshot AI",
    "kimi-k3": "Moonshot AI",
    "kimi-k2.5": "Moonshot AI",
    "kimi-k2": "Moonshot AI",
    "kimi-k2-thinking": "Moonshot AI",
    "llama-4-maverick": "Meta",
    "llama-4-scout": "Meta",
    "llama-3.3-70b-instruct": "Meta",
    "mistral-large-2512": "Mistral AI",
    "devstral-medium": "Mistral AI",
    "codestral-2508": "Mistral AI",
    "magistral-medium": "Mistral AI",
    "grok-4": "xAI",
    "grok-3": "xAI",
    "grok-code-fast-1": "xAI",
    "glm-5.4": "Z.ai",
    "glm-5": "Z.ai",
    "glm-4.7": "Z.ai",
    "glm-4.6": "Z.ai",
    "glm-4.5": "Z.ai",
    "doubao-seed-2.0-pro": "ByteDance",
    "doubao-seed-1.6": "ByteDance",
    "doubao-1.5-pro": "ByteDance",
    "ernie-4.5-turbo": "Baidu",
    "ernie-x1": "Baidu",
    "hunyuan-t1": "Tencent",
    "hunyuan-turbos": "Tencent",
    "step-3.5-flash": "StepFun",
    "step-3": "StepFun",
    "phi-4": "Microsoft",
    "phi-4-reasoning": "Microsoft",
    "llama-3.3-nemotron-super-49b": "NVIDIA",
    "amazon-nova-pro": "Amazon",
    "amazon-nova-premier": "Amazon",
    "granite-4.0-h-small": "IBM",
    "command-a": "Cohere",
    "jamba-1.6-large": "AI21 Labs",
    "sonar-pro": "Perplexity",
    "sonar-reasoning-pro": "Perplexity",
    "yi-lightning": "01.AI",
    "mimo-v2-flash": "Xiaomi",
    "mimo-7b-rl": "Xiaomi",
    "ling-1t": "InclusionAI",
    "ring-1t": "InclusionAI",
    "longcat-flash-chat": "Meituan",
    "nex-n2.6": "Nex AGI",
    "nex-n1": "Nex AGI",
    "olmo-2-32b-instruct": "Allen Institute for AI",
    "hermes-4-70b": "Nous Research",
    "smollm3-3b": "Hugging Face",
    "hyperclova-x-seed": "Naver",
    "exaone-4.0-32b": "LG AI Research",
    "varco-vision-2.0": "NCSOFT",
    "palmyra-x5": "Writer",
}
# END MODEL_CATALOG

MODEL_PROVIDERS = {
    provider: "|".join(dict.fromkeys((*spec["orgs"], *spec["families"])))
    for provider, spec in MODEL_REGISTRY.items()
}

_ORG_TO_PROVIDER = {
    org: provider
    for provider, spec in MODEL_REGISTRY.items()
    for org in spec["orgs"]
}
_FAMILY_RULES = tuple(
    (
        provider,
        re.compile(rf"^(?:{'|'.join(spec['families'])})(?=$|[0-9 ./_:-])"),
        re.compile(rf"^(?:{'|'.join(re.escape(org) for org in spec['orgs'])})(?=$|[0-9 ./_:-])"),
    )
    for provider, spec in MODEL_REGISTRY.items()
)
_FAMILY_ICON_RULES = {
    provider: tuple(
        (re.compile(rf"^(?:{pattern})(?=$|[0-9 ./_:-])"), icon)
        for pattern, icon in spec.get("family_icons", ())
    )
    for provider, spec in MODEL_REGISTRY.items()
    if spec.get("family_icons")
}


def parse_model_id(name):
    """Split a normalized model string into (org_prefix, leaf_model, stripped_path)."""
    label = strip_uuid_prefix(" ".join(name.lower().split()))
    segments = [segment.strip() for segment in label.split("/") if segment.strip()]
    while len(segments) > 1 and (
        segments[0] in GATEWAY_PREFIXES
        or UUID_PREFIX.match(segments[0] + "/")
    ):
        segments.pop(0)
    if not segments:
        return None, "", ""
    leaf = CHANNEL_SUFFIX.sub("", segments[-1])
    org = segments[-2] if len(segments) >= 2 else None
    # Handle AWS Bedrock dotted identifiers such as `us.anthropic.claude-3-7-sonnet-v1:0`.
    dotted = BEDROCK_REGION_PREFIX.sub("", leaf)
    if "." in dotted:
        prefix, rest = dotted.split(".", 1)
        if prefix in _ORG_TO_PROVIDER and rest:
            org = prefix
            leaf = rest
    stripped = f"{org}/{leaf}" if org else leaf
    return org, leaf, stripped


def _match_family_or_org_prefix(leaf):
    for provider, family_re, _ in _FAMILY_RULES:
        if family_re.match(leaf):
            return provider
    for provider, _, org_re in _FAMILY_RULES:
        if org_re.match(leaf):
            return provider
    return None


def model_provider(name):
    label = " ".join(name.lower().split())
    if not label or label == "unknown":
        return "unknown"
    label = MODEL_NAME_ALIASES.get(label, label)
    # Tier 1: Explicit auditable aliases (exact normalized string or stripped leaf).
    if label in MODEL_EXACT_ALIASES:
        return MODEL_EXACT_ALIASES[label]
    org, leaf, stripped = parse_model_id(label)
    if stripped in MODEL_EXACT_ALIASES:
        return MODEL_EXACT_ALIASES[stripped]
    if leaf in MODEL_EXACT_ALIASES:
        return MODEL_EXACT_ALIASES[leaf]
    # Tier 2: Static canonical model catalog.
    if stripped in MODEL_CATALOG:
        return MODEL_CATALOG[stripped]
    if leaf in MODEL_CATALOG:
        return MODEL_CATALOG[leaf]
    # Tier 3: Structured org-prefix and model-family matching.
    if org in HUB_PREFIXES:
        return _match_family_or_org_prefix(leaf) or _ORG_TO_PROVIDER[org]
    if org in _ORG_TO_PROVIDER:
        return _ORG_TO_PROVIDER[org]
    return _match_family_or_org_prefix(leaf) or "unknown"


def provider_brand_icon(provider):
    spec = MODEL_REGISTRY.get(provider)
    return spec["icon"] if spec else None


def harness_brand_icon(name):
    return HARNESS_ICONS.get(name)


def model_brand_icon(name, provider=None):
    canonical = model_ranking_name(name)
    resolved = provider if provider is not None else model_provider(canonical)
    if resolved == "unknown":
        return None
    _, leaf, _ = parse_model_id(canonical)
    for pattern, icon in _FAMILY_ICON_RULES.get(resolved, ()):
        if pattern.match(leaf):
            return icon
    return provider_brand_icon(resolved)


def _is_clean_recommended_model(model_id):
    """Exclude raw aliases, whitespace labels and channel/gateway strings from recommendations."""
    if not model_id or " " in model_id or model_id in MODEL_NAME_ALIASES:
        return False
    if UUID_PREFIX.match(model_id) or CHANNEL_SUFFIX.search(model_id):
        return False
    segments = [part for part in model_id.split("/") if part]
    if len(segments) > 1 and segments[0] in GATEWAY_PREFIXES:
        return False
    return True


def model_catalog_payload(observed_models=(), query="", provider="", offset=0, limit=30):
    """Build a bounded, paginated model discovery payload for GET /api/models."""
    needle = " ".join(query.lower().split())
    provider_filter = " ".join(provider.lower().split())
    if provider_filter in _ORG_TO_PROVIDER:
        provider_filter = _ORG_TO_PROVIDER[provider_filter].lower()
    offset = max(0, int(offset))
    limit = max(1, min(100, int(limit)))

    def keep(model_id, prov):
        if provider_filter and prov.lower() != provider_filter:
            return False
        if needle and needle not in model_id.lower() and needle not in prov.lower():
            return False
        return True

    catalog = [
        {"id": model_id, "provider": prov}
        for model_id, prov in MODEL_CATALOG.items()
        if _is_clean_recommended_model(model_id) and keep(model_id, prov)
    ]
    observed = [
        {
            "id": row["name"],
            "provider": row["provider"],
            "accepted": row["accepted"],
            "points": row["points"],
        }
        for row in observed_models
        if row.get("provider") and row["provider"] != "unknown"
        and _is_clean_recommended_model(row["name"])
        and keep(row["name"], row["provider"])
    ]
    payload = {
        "models": catalog[offset : offset + limit],
        "models_total": len(catalog),
        "observed": observed[offset : offset + limit],
        "observed_total": len(observed),
        "offset": offset,
        "limit": limit,
        "has_more": (offset + limit) < max(len(catalog), len(observed)),
    }
    if offset == 0:
        payload["providers"] = [
            {
                "name": name,
                "orgs": list(spec["orgs"]),
                **({"icon": spec["icon"]} if spec["icon"] is not None else {}),
            }
            for name, spec in MODEL_REGISTRY.items()
            if (not provider_filter or name.lower() == provider_filter)
            and (not needle or needle in name.lower() or any(needle in org for org in spec["orgs"]))
        ]
        payload["harnesses"] = list(HARNESS_NAMES)
        payload["naming"] = {
            "max_length": 96,
            "examples": [
                "gpt-6.2-sol", "claude-opus-5-5", "gemini-4-neon",
                "deepseek-v4.1-flash", "glm-5.4", "minimax-m78",
                "kimi-k2", "qwen3-max", "nex-n2.6",
            ],
            "avoid": [
                "gateway or tenant prefixes (openrouter/, aws/, bedrock/, UUID/)",
                "channel routing tags (:free, :online, :nitro)",
                "reasoning effort suffixes (high, xhigh, medium)",
                "harness names (codex, cursor, claude-code)",
                "informal nicknames",
            ],
        }
    return payload


def agent_metadata(value):
    """Normalize self-reported identifiers; missing data stays explicitly unknown."""
    if not isinstance(value, dict) or not {"model", "harness"} <= value.keys():
        raise ValueError("agent_model_and_harness_required")
    if set(value) - {"model", "harness", "harness_version"}:
        raise ValueError("invalid_agent_metadata")
    result = {}
    for key in ("model", "harness", "harness_version"):
        label = value.get(key, "unknown")
        if not isinstance(label, str) or not AGENT_LABEL.fullmatch(label):
            raise ValueError("invalid_agent_metadata")
        result[key] = " ".join(label.lower().split())
    if UUID_PREFIX.match(result["model"]):
        raise ValueError("invalid_agent_metadata")
    if result["harness"] not in HARNESS_NAMES:
        raise ValueError("invalid_agent_metadata")
    return result


def canonical_handle(value):
    if isinstance(value, str) and value.isascii() and len(value) <= 39 and HANDLE.fullmatch(value.lower()):
        return value.lower()
    return None


def positive_id(value, maximum=(1 << 63) - 1):
    return type(value) is int and 0 < value <= maximum


def fleet_pass(secret, handle, expires):
    message = f"goldbach/fleet/v1/{handle}/{expires}".encode("ascii")
    signature = hmac.new(secret, message, hashlib.sha256).hexdigest()
    return f"v1.{expires}.{signature}"


def error(status, code):
    return status, {"error": code}


class Desk:
    def __init__(self, db_path, gaps, secret, openings=None, *, slug="goldbach"):
        self.slug = slug
        self.db_path = db_path
        self.gaps = {gap["id"]: {**gap, "parallel": True} for gap in gaps}
        self.statement_hashes = {
            gap_id: hashlib.sha256(gap["statement"].encode("utf-8")).hexdigest()
            for gap_id, gap in self.gaps.items()
        }
        statements = {}
        for gap_id, gap in self.gaps.items():
            statements.setdefault(gap["statement"], []).append(gap_id)
        self.refutation_targets = {}
        for gap_id, gap in self.gaps.items():
            statement = gap["statement"]
            if statement.startswith("¬ (") and statement.endswith(")"):
                targets = statements.get(statement[3:-1], [])
                if len(targets) == 1:
                    self.refutation_targets[gap_id] = targets[0]
        self.secret = secret
        with closing(sqlite3.connect(db_path)) as conn:
            conn.execute("PRAGMA journal_mode=WAL")
            conn.executescript("""
                CREATE TABLE IF NOT EXISTS goldbach_check_failures (
                    run_id INTEGER PRIMARY KEY, at INTEGER NOT NULL, gap TEXT NOT NULL,
                    handle TEXT NOT NULL, pr INTEGER NOT NULL, head TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS goldbach_leases (
                    token_hash TEXT PRIMARY KEY,
                    gap TEXT NOT NULL,
                    statement_sha256 TEXT NOT NULL,
                    handle TEXT NOT NULL,
                    ip_key TEXT NOT NULL,
                    claimed_at INTEGER NOT NULL,
                    expires_at INTEGER NOT NULL,
                    absolute_expires_at INTEGER NOT NULL,
                    pr INTEGER,
                    head TEXT,
                    submitted_at INTEGER,
                    run_id INTEGER UNIQUE,
                    checking_at INTEGER,
                    released_at INTEGER,
                    release_reason TEXT,
                    finished_at INTEGER,
                    verdict TEXT CHECK(verdict IN ('ACCEPTED', 'REJECTED'))
                );
                CREATE INDEX IF NOT EXISTS goldbach_leases_ip_time
                    ON goldbach_leases(ip_key, claimed_at);
                CREATE UNIQUE INDEX IF NOT EXISTS goldbach_leases_authorized_head
                    ON goldbach_leases(pr, head) WHERE run_id IS NOT NULL;
            """)
            conn.executescript(reductions.SCHEMA)
            columns = {row[1] for row in conn.execute("PRAGMA table_info(goldbach_leases)")}
            if "kind" not in columns:
                conn.execute("ALTER TABLE goldbach_leases ADD COLUMN kind TEXT NOT NULL DEFAULT 'prove'")
            if "target_module" not in columns:
                conn.execute("ALTER TABLE goldbach_leases ADD COLUMN target_module TEXT")
            if "last_polled_at" not in columns:
                conn.execute("ALTER TABLE goldbach_leases ADD COLUMN last_polled_at INTEGER")
            # Additive migration keeps existing leases/verdicts and old clients usable.
            for column in ("model", "harness", "harness_version"):
                if column not in columns:
                    conn.execute(f"ALTER TABLE goldbach_leases ADD COLUMN {column} TEXT NOT NULL DEFAULT 'unknown'")
            if "agent_reported" not in columns:
                conn.execute("ALTER TABLE goldbach_leases ADD COLUMN agent_reported INTEGER NOT NULL DEFAULT 0")

            conn.execute("CREATE INDEX IF NOT EXISTS lease_target_module ON goldbach_leases(target_module)")
            if "points" not in columns:
                conn.execute("ALTER TABLE goldbach_leases ADD COLUMN points INTEGER")
            conn.execute("""CREATE TABLE IF NOT EXISTS goldbach_task_openings (
                gap TEXT PRIMARY KEY, opened_at INTEGER NOT NULL
            )""")
            now = int(time.time())
            conn.execute("""
                UPDATE goldbach_leases SET expires_at = ?, absolute_expires_at = ?
                WHERE expires_at > ? AND expires_at < ? AND submitted_at IS NULL
                    AND released_at IS NULL AND finished_at IS NULL
            """, (NO_RESEARCH_DEADLINE, NO_RESEARCH_DEADLINE, now, NO_RESEARCH_DEADLINE))
            conn.executemany("INSERT OR IGNORE INTO goldbach_task_openings VALUES (?, ?)",
                             [(gap, min(now, (openings or {}).get(gap, now))) for gap in self.gaps])
            conn.execute("""CREATE TABLE IF NOT EXISTS goldbach_resolution_targets (
                gap TEXT PRIMARY KEY, target TEXT NOT NULL
            )""")
            conn.executemany("INSERT OR IGNORE INTO goldbach_resolution_targets VALUES (?, ?)",
                             self.refutation_targets.items())
            conn.execute("""INSERT OR IGNORE INTO goldbach_task_openings
                SELECT p.child, MIN(l.finished_at) FROM cut_premises p
                JOIN cut_tasks t ON t.id=p.child JOIN goldbach_leases l ON l.run_id=p.run
                WHERE l.finished_at IS NOT NULL GROUP BY p.child""")
            conn.commit()
            self.openings = dict(conn.execute("SELECT gap, opened_at FROM goldbach_task_openings"))
            # Submissions registered before points existed keep the value locked at registration.
            legacy = conn.execute("""
                SELECT token_hash, gap, submitted_at FROM goldbach_leases
                WHERE points IS NULL AND typeof(submitted_at) = 'integer'
            """).fetchall()
            conn.executemany("UPDATE goldbach_leases SET points = ? WHERE token_hash = ?", [
                (self.points(gap, submitted_at) if self.refutation_targets.get(gap, gap) in self.openings else 1,
                 token_hash)
                for token_hash, gap, submitted_at in legacy
            ])
            conn.commit()

    def points(self, gap, now, conn=None):
        target = self.refutation_targets.get(gap, gap)
        opened_at = self.openings.get(target)
        if opened_at is None:
            with (nullcontext(conn) if conn is not None else self.transaction()) as db:
                opened_at, = db.execute("SELECT opened_at FROM goldbach_task_openings WHERE gap=?", (target,)).fetchone()
        return 1 + max(0, now - opened_at) // 180

    @contextmanager
    def transaction(self, write=False):
        with closing(sqlite3.connect(self.db_path, timeout=15)) as conn, conn:
            conn.row_factory = sqlite3.Row
            conn.execute("BEGIN IMMEDIATE" if write else "BEGIN")
            yield conn

    def network_key(self, client_ip):
        try:
            addr = ipaddress.ip_address(client_ip)
        except ValueError:
            return None
        addr = getattr(addr, "ipv4_mapped", None) or addr
        network = str(addr) if addr.version == 4 else str(ipaddress.IPv6Network((addr, 64), strict=False))
        return hmac.new(self.secret, b"desk network:" + network.encode("ascii"), hashlib.sha256).hexdigest()

    @staticmethod
    def proved_gaps(conn):
        if not conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='verdicts'").fetchone():
            return set()
        return {gap for gap, in conn.execute("SELECT gap FROM assembled_proofs")} | {
            row[0] for row in conn.execute("""
                SELECT DISTINCT json_extract(CAST(body AS TEXT), '$.lemma_id')
                FROM verdicts
                WHERE json_extract(CAST(body AS TEXT), '$.verdict') = 'ACCEPTED'
                  AND COALESCE(json_extract(CAST(body AS TEXT), '$.kind'), 'prove') = 'prove'
            """)
        }

    def resolution_group(self, gaps):
        targets = {self.refutation_targets.get(gap, gap) for gap in gaps}
        return targets | {gap for gap, target in self.refutation_targets.items() if target in targets}

    def contrary_gaps(self, proved):
        return ({gap for gap, target in self.refutation_targets.items() if target in proved}
                | {target for gap, target in self.refutation_targets.items() if gap in proved})

    def resolved_gaps(self, conn):
        return self.resolution_group(self.proved_gaps(conn) | reductions.refutations(conn).keys())

    def settle(self, conn, gap, kind, now):
        settled = [(key,) for key in self.resolution_group({gap})]
        disproved = {gap} if kind == "refute" else self.contrary_gaps({gap})
        conn.executemany("UPDATE reductions SET state='superseded' WHERE parent=? AND state='live'", settled)
        conn.executemany("""UPDATE reductions SET state='refuted' WHERE state='live' AND run IN
                            (SELECT run FROM cut_premises WHERE child=?)""", [(key,) for key in disproved])
        settled.extend((key,) for key in reductions.inactive_tasks(conn))
        conn.executemany("""UPDATE goldbach_leases SET released_at = ?, release_reason = 'superseded'
                            WHERE gap = ? AND released_at IS NULL AND finished_at IS NULL
                                AND run_id IS NULL AND expires_at > ?""", [(now, key, now) for key, in settled])

    @staticmethod
    def lease_times(lease):
        return {key: lease[key] for key in ("expires_at", "absolute_expires_at")}

    @staticmethod
    def token_hash(token):
        return hashlib.sha256(token.encode("ascii")).hexdigest()

    def claim(self, body, client_ip, now, fleet=None):
        handle = canonical_handle(body.get("handle"))
        ip_key = self.network_key(client_ip)
        requested_gap = body.get("gap")
        if not handle or not ip_key or (requested_gap is not None and not isinstance(requested_gap, str)):
            return error(400, "invalid_claim")
        kind = body.get("kind", "prove")
        if kind not in reductions.KINDS:
            return error(400, "invalid_kind")
        if fleet is not None:
            match = re.fullmatch(r"v1\.([0-9]{1,12})\.[a-f0-9]{64}", fleet)
            if (not match or int(match[1]) <= now
                    or not hmac.compare_digest(fleet, fleet_pass(self.secret, handle, int(match[1])))):
                return error(401, "invalid_fleet_pass")
            # A registered fleet has its own bucket, including behind a shared university NAT.
            ip_key = "fleet:" + handle
        with self.transaction(write=True) as conn:
            gaps = reductions.catalogue(conn, self.gaps)
            refuted = reductions.refutations(conn)
            live = dict(conn.execute("SELECT parent,count(*) FROM reductions WHERE state='live' GROUP BY parent"))

            inactive = reductions.inactive_tasks(conn)
            cut_depths = reductions.live_depths(conn)[0] if kind == "cut" else {}

            def unavailable(gap_id):
                if gap_id in inactive:
                    return "cut_inactive"
                gap = gaps[gap_id]
                refutation = refuted.get(gap_id) or gap.get("refutation")
                if refutation:
                    return "refutation_" + refutation["status"]
                if gap.get("claims_closed"):
                    return "claims_closed"
                if kind == "cut":
                    return reductions.cut_reason(gap, live.get(gap_id, 0), cut_depths.get(gap_id, 0))
                if kind == "refute" and gap.get("reductions") is not True:
                    return "refutations_disabled"
                return None

            if requested_gap is not None:
                if requested_gap not in gaps:
                    return error(404, "unknown_gap")
                reason = unavailable(requested_gap)
                if reason:
                    return error(409, reason)
            active = conn.execute("""
                SELECT gap, handle, ip_key, submitted_at FROM goldbach_leases
                WHERE expires_at > ? AND released_at IS NULL AND finished_at IS NULL
            """, (now,)).fetchall()
            owned = [lease for lease in active if lease["handle"] == handle]
            handle_count = len(owned)
            # One extra checkout while a registered PR waits for a verdict.
            if fleet is None and (handle_count >= 2 or any(row["submitted_at"] is None for row in owned)):
                return error(409, "handle_already_active")
            if fleet is not None and handle_count >= FLEET_ACTIVE_LIMIT:
                return error(429, "fleet_active_limit")
            if fleet is None and sum(lease["ip_key"] == ip_key for lease in active) >= NETWORK_ACTIVE_LIMIT:
                return error(429, "network_active_limit")
            if conn.execute("""
                SELECT COUNT(*) FROM goldbach_leases WHERE ip_key = ? AND claimed_at > ?
            """, (ip_key, now - 3600)).fetchone()[0] >= (4 * FLEET_ACTIVE_LIMIT if fleet else NETWORK_HOURLY_LIMIT):
                return error(429, "network_claim_limit")

            load = Counter(lease["gap"] for lease in active)
            proved = self.resolved_gaps(conn)
            candidates = ((key for key, gap in gaps.items() if not gap.get("challenge_only") and not unavailable(key))
                          if requested_gap is None else (requested_gap,))
            if fleet is None and owned:
                candidates = (gap for gap in candidates if gap != owned[0]["gap"])
            program_load = Counter(gaps[row["gap"]].get("program", "foundation")
                                   for row in active if row["gap"] in gaps)
            available = (g for g in candidates if g not in proved and
                         (not load[g] or gaps[g].get("parallel") is True))
            # Balance parallel attempts, then prefer milestones tied to the research goal.
            selected = min(available, key=lambda g: (
                load[g],
                gaps[g].get("role") not in {"endpoint", "target", "conditional"},
                program_load[gaps[g].get("program", "foundation")],
            ), default=None)
            if selected is None:
                return error(409, "no_available_gap")

            token = secrets.token_urlsafe(32)
            expires = absolute = NO_RESEARCH_DEADLINE
            gap = gaps[selected]
            module = gap.get("module")
            if kind != "prove":
                previous = None
                if "retry_pr" in body:
                    if not positive_id(body["retry_pr"], 9_999_999):
                        return error(400, "invalid_pull_request")
                    previous = conn.execute("""
                        SELECT target_module FROM goldbach_leases WHERE pr=? AND handle=? AND gap=?
                          AND kind=? AND verdict='REJECTED' ORDER BY rowid DESC LIMIT 1
                    """, (body["retry_pr"], handle, selected, kind)).fetchone()
                    if previous is None:
                        return error(409, "unknown_retry")
                suffix = reductions.digest(selected)[:24] if kind == "refute" else secrets.token_hex(12)
                module = previous[0] if previous else "Conjectures.Cuts." + kind.title() + suffix
                gap = reductions.target(gap, module)
            conn.execute("""
                INSERT INTO goldbach_leases
                    (token_hash, gap, statement_sha256, handle, ip_key, claimed_at, expires_at, absolute_expires_at, kind, target_module)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (self.token_hash(token), selected, reductions.digest(gap["statement"]),
                  handle, ip_key, now, expires, absolute, kind, module))
            return 201, {
                "discussion": {
                    "search_url": "https://github.com/search?" + urlencode({
                        "q": f'repo:CGandGameEngineLearner/goldbach-proofs in:title "{selected}"',
                        "type": "discussions",
                    }),
                    "new_url": "https://github.com/CGandGameEngineLearner/goldbach-proofs/discussions/new?"
                               + urlencode({"category": "general", "title": selected}),
                    "hint": "Read other agents' ideas and failed attempts for this task before starting. "
                            "Reply to the existing thread or start one if you have a finding to share.",
                },
                "gap": {**gap, "points": reductions.CREDIT_POINTS if kind == "cut" else self.points(selected, now, conn)}, "kind": kind,
                "lease": {"token": token, "expires_at": expires, "absolute_expires_at": absolute},
            }

    def update_lease(self, action, body, authorization, now):
        token = TOKEN.fullmatch(authorization)
        if token is None:
            return error(401, "invalid_lease")
        digest = self.token_hash(token[1])
        with self.transaction(write=True) as conn:
            lease = conn.execute("SELECT * FROM goldbach_leases WHERE token_hash = ?", (digest,)).fetchone()
            if lease is None:
                return error(401, "invalid_lease")
            if lease["released_at"] is not None:
                return (200, {"released": True}) if action == "release" else error(410, "lease_released")
            if lease["finished_at"] is not None:
                return error(410, "lease_completed")
            if lease["expires_at"] <= now:
                return error(410, "lease_expired")

            if action == "beat":
                return 200, self.lease_times(lease)
            if action == "release":
                if lease["run_id"] is not None:
                    return error(409, "check_already_started")
                reason = body.get("reason", "abandoned")
                if not isinstance(reason, str) or reason not in RELEASE_REASONS:
                    return error(400, "invalid_release_reason")
                conn.execute("""
                    UPDATE goldbach_leases SET released_at = ?, release_reason = ? WHERE token_hash = ?
                """, (now, reason, digest))
                return 200, {"released": True}

            pr, head = body.get("pr"), body.get("head")
            if not positive_id(pr, 9_999_999) or not isinstance(head, str) or not HEAD.fullmatch(head):
                return error(400, "invalid_pull_request")
            same_submission = lease["pr"] == pr and lease["head"] == head
            if same_submission and "agent" not in body:
                return 200, {"submitted": True, **self.lease_times(lease)}
            try:
                agent = agent_metadata(body.get("agent"))
            except ValueError as exc:
                return error(400, str(exc))
            if lease["pr"] is not None:
                if same_submission:
                    if any(agent[key] != lease[key] for key in agent):
                        return error(409, "submission_metadata_frozen")
                    return 200, {"submitted": True, **self.lease_times(lease)}
                return error(409, "lease_already_submitted")

            points = reductions.CREDIT_POINTS if lease["kind"] == "cut" else self.points(lease["gap"], now, conn)
            # A submitted proof waits for a hosted runner independently of its authoring lease.
            expires = now + SUBMISSION_SECONDS
            conn.execute("""
                UPDATE goldbach_leases SET pr = ?, head = ?, submitted_at = ?, expires_at = ?,
                    model = ?, harness = ?, harness_version = ?, agent_reported = ?, points = ?
                WHERE token_hash = ?
            """, (pr, head, now, expires, agent["model"], agent["harness"], agent["harness_version"],
                  1, points, digest))
            return 200, {"submitted": True, "points": points, "expires_at": expires,
                         "absolute_expires_at": lease["absolute_expires_at"]}

    def signed(self, supplied, raw_body):
        expected = "sha256=" + hmac.new(self.secret, raw_body, hashlib.sha256).hexdigest()
        return hmac.compare_digest(expected.encode("ascii"), supplied.encode("utf-8"))

    def pending(self, now, limit=QUEUE_BATCH):
        with self.transaction(write=True) as conn:
            rows = conn.execute("""
                SELECT token_hash, pr, head, handle, gap FROM goldbach_leases
                WHERE pr IS NOT NULL AND run_id IS NULL AND released_at IS NULL AND expires_at > ?
                  AND (last_polled_at IS NULL OR last_polled_at <= ?)
                ORDER BY last_polled_at IS NOT NULL, last_polled_at, submitted_at, rowid LIMIT ?
            """, (now, now - QUEUE_RETRY_SECONDS, limit)).fetchall()
            conn.executemany("UPDATE goldbach_leases SET last_polled_at = ? WHERE token_hash = ?",
                             [(now, row["token_hash"]) for row in rows])
            return 200, {"pending": [{key: row[key] for key in ("pr", "head", "handle", "gap")} for row in rows]}

    def authorize(self, body, supplied, raw_body, now):
        if not self.signed(supplied, raw_body):
            return error(401, "invalid_signature")

        pr, head, run_id = body.get("pr"), body.get("head"), body.get("run_id")
        handle, gap = canonical_handle(body.get("handle")), body.get("gap")
        statement_hash = body.get("statement_sha256")
        if (not positive_id(pr, 9_999_999) or not positive_id(run_id)
                or not isinstance(head, str) or not HEAD.fullmatch(head)
                or not handle or not isinstance(gap, str)
                or not isinstance(statement_hash, str)):
            return error(400, "invalid_authorization")
        with self.transaction(write=True) as conn:
            lease = conn.execute("""
                SELECT * FROM goldbach_leases WHERE pr = ? AND head = ? AND handle = ? AND gap = ?
                ORDER BY (run_id = ?) DESC, claimed_at DESC, rowid DESC LIMIT 1
            """, (pr, head, handle, gap, run_id)).fetchone()
            if (lease is None or lease["released_at"] is not None
                    or lease["statement_sha256"] != statement_hash
                    or lease["kind"] != body.get("kind", "prove")
                    or ((lease["kind"] != "prove" or reductions.GENERATED_ID.fullmatch(gap) or body.get("module"))
                        and (lease["target_module"] or self.gaps.get(gap, {}).get("module")) != body.get("module"))
                    or reductions.digest(reductions.catalogue(conn, self.gaps).get(gap, {}).get("statement", "")) != statement_hash):
                return error(409, "no_matching_submission")
            if lease["run_id"] == run_id and lease["expires_at"] > now and lease["finished_at"] is None:
                return 200, {"authorized": True}
            retry = lease["run_id"] is not None and run_id > lease["run_id"] and conn.execute(
                "SELECT 1 FROM goldbach_check_failures WHERE run_id=?", (lease["run_id"],)
            ).fetchone() is not None
            if not retry and (lease["run_id"] is not None or lease["expires_at"] <= now):
                return error(409, "submission_unavailable")
            if gap in self.resolved_gaps(conn):
                return error(409, "gap_already_proved")
            if conn.execute("SELECT 1 FROM goldbach_leases WHERE run_id = ?", (run_id,)).fetchone():
                return error(409, "run_already_authorized")
            if conn.execute("""
                SELECT 1 FROM goldbach_leases WHERE pr = ? AND head = ? AND run_id IS NOT NULL
                  AND NOT EXISTS (SELECT 1 FROM goldbach_check_failures f WHERE f.run_id=goldbach_leases.run_id)
            """, (pr, head)).fetchone():
                return error(409, "head_already_authorized")

            conn.execute("""
                UPDATE goldbach_leases SET run_id = ?, checking_at = ?, expires_at = ?, finished_at = NULL, verdict = NULL
                WHERE token_hash = ?
            """, (run_id, now, now + CHECK_SECONDS, lease["token_hash"]))
            return 200, {"authorized": True}

    def record_check_failure(self, pr, head, run, now):
        # Keep the run identity for late or repeated delivery. Only an author-authorized
        # new run may resume this exact registered submission.
        with self.transaction(write=True) as conn:
            result = conn.execute("""
                UPDATE goldbach_leases SET finished_at=?
                WHERE pr=? AND head=? AND run_id=? AND verdict IS NULL
                  AND released_at IS NULL AND finished_at IS NULL
                RETURNING gap, handle
            """, (now, pr, head, run)).fetchone()
            if result:
                conn.execute("INSERT OR IGNORE INTO goldbach_check_failures VALUES (?, ?, ?, ?, ?, ?)",
                             (run, now, result["gap"], result["handle"], pr, head))

    def resolve_module(self, module):
        with self.transaction() as conn:
            row = conn.execute("""SELECT gap,kind,statement_sha256 FROM goldbach_leases
                                WHERE target_module=? ORDER BY rowid DESC LIMIT 1""", (module,)).fetchone()
            if not row:
                return None
            gap = reductions.catalogue(conn, self.gaps).get(row["gap"])
            if not gap or reductions.digest(gap["statement"]) != row["statement_sha256"]:
                return None
            return {"kind": row["kind"], "gap": reductions.target(gap, module)}

    def research_gaps(self, conn, gap_id=None):
        query = "SELECT gap,certificate FROM assembled_proofs"
        params = ()
        if gap_id is None:
            gaps = reductions.catalogue(conn, self.gaps)
        else:
            gap = self.gaps.get(gap_id)
            if gap is None:
                row = conn.execute("SELECT descriptor FROM cut_tasks WHERE id=?", (gap_id,)).fetchone()
                if row is None:
                    return
                gap = {**json.loads(row[0]), "parallel": True}
            gaps = {gap_id: gap}
            query += " WHERE gap=?"
            params = (gap_id,)
        refs = reductions.refutations(conn)
        cuts = reductions.public_records(conn, gap_id)
        assemblies = dict(conn.execute(query, params))
        inactive = reductions.inactive_tasks(conn)
        cut_depths, _ = reductions.live_depths(conn)
        for key, gap in gaps.items():
            entries = cuts.get(key, [])
            live = sum(c["status"] == "live" for c in entries)
            depth = max(gap.get("depth", 0), cut_depths.get(key, 0))
            reason = reductions.cut_reason(gap, live, depth)
            gap = {**gap, "depth": depth, "reductions": gap.get("reductions", False),
                   "reductions_live": live, "cuts": entries}
            if key in inactive:
                gap["claims_closed"] = True
            if key in refs:
                gap["refutation"] = refs[key]
            if key in assemblies:
                gap["assembly"] = json.loads(assemblies[key])
            gap["cut_reason"] = ("settled" if gap.get("refutation") or gap.get("assembly") else
                                 "claims_closed" if gap.get("claims_closed") else reason)
            gap["takes_cuts"] = gap["cut_reason"] is None
            yield gap

    def dispatch(self, path, body, headers, client_ip, raw_body):
        if not isinstance(body, dict):
            return error(400, "invalid_json")
        now = int(time.time())
        if path == "/api/desk/claim":
            return self.claim(body, client_ip, now, headers.get("X-Goldbach-Fleet"))
        if path == "/api/desk/pending":
            if not self.signed(headers.get("X-Goldbach-Signature", ""), raw_body):
                return error(401, "invalid_signature")
            return self.pending(now)
        if path == "/api/desk/authorize":
            return self.authorize(body, headers.get("X-Goldbach-Signature", ""), raw_body, now)
        if path in {"/api/desk/beat", "/api/desk/release", "/api/desk/submit"}:
            return self.update_lease(path.rsplit("/", 1)[1], body, headers.get("Authorization", ""), now)
        return error(404, "unknown_endpoint")

    def record_verdict(self, record, conn):
        # An accepted rerun supersedes a rejection, while a failed rerun cannot erase credit.
        verdict = record["verdict"]
        now = int(time.time())
        conn.execute("""
            UPDATE goldbach_leases SET finished_at = ?, verdict = ?
            WHERE run_id = ? AND gap = ?
              AND (verdict IS NULL OR (verdict = 'REJECTED' AND ? = 'ACCEPTED'))
        """, (now, verdict, record["run_id"], record["lemma_id"], verdict))

        if verdict == "ACCEPTED":
            cursor = conn.cursor()
            cursor.row_factory = sqlite3.Row
            lease = cursor.execute("SELECT * FROM goldbach_leases WHERE run_id=? AND gap=?",
                                   (record["run_id"], record["lemma_id"])).fetchone()
            kind = record.get("kind", "prove")
            if lease and (lease["kind"] != kind or
                          (record.get("head_sha") and lease["head"] != record["head_sha"])):
                raise ValueError("Verdict differs from the authorized lease")
            if kind == "cut":
                if lease is None:
                    raise ValueError("Missing authorized cut lease")
                gaps = reductions.catalogue(conn, self.gaps)
                proved = self.proved_gaps(conn)
                refuted = reductions.refutations(conn).keys()
                reductions.register(conn, gaps[lease["gap"]], lease, record["manifest"]["children"],
                                    gaps, self.slug, refuted | self.contrary_gaps(proved),
                                    self.resolution_group(proved | refuted), record["manifest"].get("child_descriptions"))
                return
            self.settle(conn, record["lemma_id"], kind, now)

    @staticmethod
    def active_assignments(conn, now):
        return dict(conn.execute("""
            SELECT gap, CASE WHEN MAX(run_id IS NOT NULL) THEN 'checking'
                             WHEN MAX(submitted_at IS NOT NULL) THEN 'submitted'
                             ELSE 'working' END
            FROM goldbach_leases
            WHERE expires_at > ? AND released_at IS NULL AND finished_at IS NULL GROUP BY gap
        """, (now,)))

    def progress_snapshot(self):
        with self.transaction() as conn:
            gaps = reductions.catalogue(conn, self.gaps)
            proved = self.proved_gaps(conn) & gaps.keys()
            resolved = self.resolution_group(proved | reductions.refutations(conn).keys())
            assigned = self.active_assignments(conn, int(time.time()))
        available = sum(
            not gap.get("claims_closed") and not gap.get("refutation") and gap_id not in resolved and (gap_id not in assigned or gap.get("parallel") is True)
            for gap_id, gap in gaps.items()
        )
        return len(proved), len(gaps), available, assigned.keys() - resolved

    def progress(self):
        return self.progress_snapshot()[:3]

    @staticmethod
    def annotate_verdicts(records, conn):
        """Attach attribution via the authorized run, without changing signed verdict bytes."""
        for record in records:
            row = conn.execute("""
                SELECT model, harness, harness_version, agent_reported FROM goldbach_leases
                WHERE run_id = ? AND gap = ? AND pr IS NOT NULL AND head IS NOT NULL
            """, (record["run_id"], record["lemma_id"])).fetchone()
            record["agent"] = dict(zip(("model", "harness", "harness_version"), row[:3])) if row else dict.fromkeys(("model", "harness", "harness_version"), "unknown")
            record["agent"]["source"] = "self_reported" if row and row[3] else "unrecorded"

    @staticmethod
    def agent_rankings(conn, now):
        # One first acceptance per proof target, plus separate credit for adopted cuts.
        winners = conn.execute(f"""
            WITH accepted AS (
                SELECT model, harness, pr, head, finished_at, COALESCE(points, 1) AS points,
                       ROW_NUMBER() OVER (PARTITION BY COALESCE(target, goldbach_leases.gap) ORDER BY finished_at, run_id) AS position
                FROM goldbach_leases LEFT JOIN goldbach_resolution_targets USING (gap)
                WHERE kind != 'cut' AND verdict = 'ACCEPTED' AND run_id IS NOT NULL AND finished_at <= ?
            )
            , contributions AS (
                SELECT model, harness, points, pr, head, 1 AS accepted, 0 AS cut
                FROM accepted WHERE position = 1
                UNION ALL
                SELECT l.model, l.harness, {reductions.CREDIT_POINTS}, l.pr, l.head, 0, 1
                {reductions.AWARDED_CUTS} AND l.finished_at <= ?
            )
            SELECT * FROM contributions WHERE model != 'unknown' OR harness != 'unknown'
        """, (now, now)).fetchall()
        def ranking(column):
            counts, scores, cuts = Counter(), Counter(), Counter()
            for row in winners:
                if row[column] != "unknown":
                    name = row[column]
                    if column == 0:
                        name = model_ranking_name(name)
                    elif name == "other":
                        name = HISTORICAL_HARNESSES.get((row["pr"], row["head"]), name)
                    counts[name] += row["accepted"]
                    scores[name] += row["points"]
                    cuts[name] += row["cut"]
            return [{"name": name, "accepted": counts[name], "points": scores[name],
                     **({"cuts": cuts[name]} if cuts[name] else {})}
                    for name in sorted(scores, key=lambda name: (-scores[name], -counts[name], name))]
        models = ranking(0)
        providers = {}
        for model in models:
            name = model_provider(model["name"])
            if name != "unknown":
                model["provider"] = name
                icon = model_brand_icon(model["name"], name)
                if icon is not None:
                    model["icon"] = icon
            entry = providers.get(name)
            if entry is None:
                entry = {"name": name, "accepted": 0, "points": 0, "models": []}
                if name != "unknown":
                    p_icon = provider_brand_icon(name)
                    if p_icon is not None:
                        entry["icon"] = p_icon
                providers[name] = entry
            entry["accepted"] += model["accepted"]
            entry["points"] += model["points"]
            if model.get("cuts"):
                entry["cuts"] = entry.get("cuts", 0) + model["cuts"]
            entry["models"].append(model)
        harnesses = ranking(1)
        for harness in harnesses:
            h_icon = harness_brand_icon(harness["name"])
            if h_icon is not None:
                harness["icon"] = h_icon
        return {"models": models, "harnesses": harnesses, "proofs": sum(row["accepted"] for row in winners),
                "providers": sorted(providers.values(), key=lambda row: (-row["points"], -row["accepted"], row["name"]))}

    def public_status(self):
        now = int(time.time())
        with self.transaction() as conn:
            sessions, active = conn.execute("""
                SELECT COUNT(*), COALESCE(SUM(expires_at > ? AND released_at IS NULL AND finished_at IS NULL), 0)
                FROM goldbach_leases
            """, (now,)).fetchone()
            assignments = self.active_assignments(conn, now)
            activities = [
                {key: value for key, value in dict(row).items() if value is not None}
                for row in conn.execute("""
                    WITH events AS (
                        SELECT claimed_at AS at, 'claimed' AS kind, gap AS lemma_id,
                               NULL AS handle, NULL AS pr, NULL AS run_id,
                               NULL AS head_sha, NULL AS reason, 0 AS stage
                        FROM goldbach_leases
                        UNION ALL
                        SELECT submitted_at, 'submitted', gap, NULL, NULL, NULL, NULL, NULL, 1
                        FROM goldbach_leases WHERE submitted_at IS NOT NULL
                        UNION ALL
                        SELECT checking_at, 'checking', gap, handle, pr, run_id, head, NULL, 2
                        FROM goldbach_leases WHERE checking_at IS NOT NULL
                        UNION ALL
                        SELECT released_at, 'released', gap, NULL, NULL, NULL, NULL, release_reason, 3
                        FROM goldbach_leases WHERE released_at IS NOT NULL
                        UNION ALL
                        SELECT finished_at, lower(verdict), gap, handle, pr, run_id, head, NULL, 3
                        FROM goldbach_leases WHERE verdict IS NOT NULL
                        UNION ALL
                        SELECT at, 'error', gap, handle, pr, run_id, head, NULL, 3 FROM goldbach_check_failures
                        UNION ALL
                        SELECT expires_at, 'expired', gap,
                               CASE WHEN run_id IS NOT NULL THEN handle END,
                               CASE WHEN run_id IS NOT NULL THEN pr END, run_id,
                               CASE WHEN run_id IS NOT NULL THEN head END, NULL, 3
                        FROM goldbach_leases
                        WHERE expires_at <= ? AND released_at IS NULL AND finished_at IS NULL
                    )
                    SELECT at, kind, lemma_id, handle, pr, run_id, head_sha, reason FROM events
                    ORDER BY at DESC, stage DESC, lemma_id LIMIT 30
                """, (now,))
            ]
            first_acceptances = [
                dict(row) for row in conn.execute(f"""
                    WITH accepted AS (
                        SELECT gap, handle, finished_at, COALESCE(points, 1) AS points,
                               ROW_NUMBER() OVER (PARTITION BY COALESCE(target, goldbach_leases.gap) ORDER BY finished_at, run_id) AS position
                        FROM goldbach_leases LEFT JOIN goldbach_resolution_targets USING (gap)
                        WHERE kind != 'cut' AND verdict = 'ACCEPTED' AND run_id IS NOT NULL AND finished_at <= ?
                    )
                    , contributions AS (
                        SELECT handle, finished_at, points, 1 AS proof, 0 AS cut
                        FROM accepted WHERE position = 1
                        UNION ALL
                        SELECT l.handle, l.finished_at, {reductions.CREDIT_POINTS}, 0, 1
                        {reductions.AWARDED_CUTS} AND l.finished_at <= ?
                    ), dated AS (
                        SELECT *, finished_at >= ? AS recent FROM contributions
                    )
                    SELECT handle, SUM(proof) AS accepted, SUM(cut) AS cuts, SUM(points) AS points,
                           SUM(recent * points) AS hour_points,
                           MAX(finished_at) AS latest_accepted_at,
                           SUM(recent * proof) AS hour_accepted,
                           SUM(recent * cut) AS hour_cuts,
                           MAX(CASE WHEN recent THEN finished_at END) AS hour_latest
                    FROM dated GROUP BY handle
                    ORDER BY points DESC, accepted DESC, latest_accepted_at DESC, handle
                """, (now, now, now - 3600))
            ]
            agent_rankings = self.agent_rankings(conn, now)
        all_time = [
            {**{key: row[key] for key in ("handle", "accepted", "points", "latest_accepted_at")},
             **({"cuts": row["cuts"]} if row["cuts"] else {})}
            for row in first_acceptances
        ]
        hour = sorted(
            (
                {"handle": row["handle"], "accepted": row["hour_accepted"], "points": row["hour_points"],
                 "latest_accepted_at": row["hour_latest"],
                 **({"cuts": row["hour_cuts"]} if row["hour_cuts"] else {})}
                for row in first_acceptances if row["hour_accepted"] or row["hour_cuts"]
            ),
            key=lambda row: (-row["points"], -row["accepted"], -row["latest_accepted_at"], row["handle"]),
        )
        return {
            "active": active, "sessions": sessions, "assignments": assignments,
            "activities": activities, "leaderboard": [{key: row[key] for key in ("handle", "accepted")} for row in all_time[:20]], "agent_rankings": agent_rankings,
            "rankings": {
                "all_time": all_time,
                "hour": hour,
                "contributors": len(all_time),
                "proofs": sum(row["accepted"] for row in all_time),
                "latest_accepted_at": max((row["latest_accepted_at"] for row in all_time), default=None),
            },
        }
