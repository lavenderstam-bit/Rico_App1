import flet as ft
#import speech_recognition as sr
import gspread
from oauth2client.service_account import ServiceAccountCredentials
from datetime import datetime, timedelta
import re
import os
import sys
import time
import threading
import warnings
import difflib
import random
import socket
import json
import csv
import base64
import smtplib
import traceback
import tempfile
from email.mime.text import MIMEText

warnings.filterwarnings("ignore")

# ---------------------------------------------------------
# دالة مساعدة لتحديد مسار الملفات (معدلة ومحسنة)
# ---------------------------------------------------------
def resource_path(relative_path):
    """ Get absolute path to resource, works for dev and for PyInstaller """
    try:
        # PyInstaller creates a temp folder and stores path in _MEIPASS
        base_path = sys._MEIPASS
    except Exception:
        # في حالة الكود العادي: استخدم مسار الملف الحالي بدقة
        base_path = os.path.dirname(os.path.abspath(__file__))

    return os.path.join(base_path, relative_path)

# ---------------------------------------------------------
# 1. إعدادات المتغيرات العامة
# ---------------------------------------------------------

app_state = {
    "header_text": "🚀 جاري بدء النظام...",
    "header_color": "orange",
    "timer_text": "⏱️ 00:00:00",
    "mic_status": "idle",
    "data_ready": False,
    "last_command": "",
    "user_name": "",
    "confirm_save_flag": False,
    "row_to_edit": None,
    "row_to_delete": None,
    "current_rep_target": "",
    "silence_counter": 0,
    "current_page": "reg",
    "is_dialog_open": False,
    "is_loading": False,
    "voice_mode": False,
    "is_offline": False,
    "user_role": "user"}

custom_date_state = {"day": "", "month": "", "year": ""}

rep_state = {
    "entity": "الكل",
    "period": "الشهر الحالي",
    "main": "الكل",
    "sub": "الكل"
}

PAYMENT_OPTS = {}
raw_data = []
config_data = []
users_db = {} 

# كوبري لتشغيل الصوت من أي مكان في الكود
global_speak_bridge = None

def speak(text):
    if global_speak_bridge:
        global_speak_bridge(text)

def encode_base64(data_str):
    return base64.b64encode(data_str.encode("utf-8")).decode("utf-8")

def decode_base64(enc_str):
    return base64.b64decode(enc_str.encode("utf-8")).decode("utf-8")

# القاموس الذكي
control_dict = {
    "synonyms": {
        "مصاريف": "مصروف", "صرفت": "مصروف", "اشتريت": "مصروف",
        "دخل": "إيراد", "قبضت": "إيراد", "مبيعات": "إيراد", "ايراد": "إيراد",
        "حول": "تحويل داخلي", "نقل": "تحويل عهدة",
        "البيت": "البيت", "المكتبة": "لافندر", "مكتبة": "لافندر"
    }, 
    "nav": {
        "تسجيل": "reg", "الرئيسية": "reg", "سجل": "reg",
        "أرصدة": "bal", "رصيد": "bal", "الارصدة": "bal", "الأرصدة": "bal", "الرصيد": "bal", "وريني الرصيد": "bal",
        "عمليات": "trans", "العمليات": "trans",
        "تقارير": "reports", "تقرير": "reports", "التقارير": "reports",
        "جرد": "cash", "عد": "cash", "نقدية": "cash", "نقديه": "cash", "جرد النقدية": "cash"
    }, 
    "defaults": {}
}

control_list_view = ft.ListView(expand=True, spacing=5)

STOP_WORDS = [
    "يا", "ريكو", "سجل", "سجلي", "اكتب", "حط", "ضيف", "إضافة",
    "الكيان", "المصدر", "كيان", "مصدر",
    "التصنيف", "الرئيسي", "الفرعي", "نوع", "العملية",
    "مبلغ", "فلوس", "قدره", "بقيمة", "بتاع",
    "جنيه", "جنية", "ريال", "دولار",
    "هات", "وريني", "اعرض", "افتح", "عايز", "عاوز", "خش", "علي", "على", "صفحة", "شاشة",
    "من", "إلى", "الي", "في", "لـ", "عدد", "عددهم", "فئة", "ال", "ورقة", "خانه", "خانة"
]

TEXT_TO_NUM = {
    "واحد": 1, "واحده": 1, "واحدة": 1,
    "اثنين": 2, "اتنين": 2,
    "ثلاثة": 3, "تلاته": 3, "ثلاثه": 3, "تلاتة": 3,
    "أربعة": 4, "اربعة": 4, "اربع": 4,
    "خمسة": 5, "خمس": 5,
    "ستة": 6, "ست": 6,
    "سبعة": 7, "سبع": 7,
    "ثمانية": 8, "تمانية": 8,
    "تسعة": 9, "تسع": 9,
    "عشرة": 10, "عشر": 10
}

ARABIC_DAYS = {
    "Saturday": "السبت", "Sunday": "الأحد", "Monday": "الاثنين",
    "Tuesday": "الثلاثاء", "Wednesday": "الأربعاء", "Thursday": "الخميس",
    "Friday": "الجمعة"
}


log_view = ft.ListView(expand=True, spacing=2, auto_scroll=True)

def add_log(message, color="black"):
    try:
        timestamp = datetime.now().strftime("%H:%M:%S")
        log_view.controls.append(ft.Text(f"[{timestamp}] {message}", color=color, size=11, font_family="Consolas"))
        log_view.update()
    except: pass

def clean_text(text):
    words = text.split()
    filtered = [w for w in words if w not in STOP_WORDS]
    return " ".join(filtered)

def normalize_word(word):
    if not word: return ""
    word = word.strip()
    if word.startswith("ال"): word = word[2:]
    word = word.replace("أ", "ا").replace("إ", "ا").replace("آ", "ا")
    if word.endswith("ة"): word = word[:-1] + "ه"
    if word.endswith("ات") and len(word) > 4: word = word[:-2]
    if word.startswith("اس") and len(word) > 4: word = word[2:] 
    return word

def fuzzy_match(target, options, cutoff=0.5):
    if not target or not options: return None
    target_norm = normalize_word(target)
    for opt in options:
        opt_norm = normalize_word(opt)
        if target_norm in opt_norm or opt_norm in target_norm:
            return opt
    normalized_options = {normalize_word(opt): opt for opt in options}
    matches = difflib.get_close_matches(target_norm, normalized_options.keys(), n=1, cutoff=cutoff)
    if matches:
        return normalized_options[matches[0]]
    return None

def get_safe_balance(safe_name):
    if not raw_data: return 0
    balance = 0
    safe_name = str(safe_name).strip()
    for row in raw_data:
        if len(row) < 9: continue
        try:
            r_amount = float(row[1]) if row[1] else 0
            r_method = str(row[6]).strip() if row[6] else ""
            r_type = str(row[8]).strip() if row[8] else ""
            should_count = False
            if safe_name == "الكل":
                if r_method: should_count = True
            elif r_method == safe_name:
                should_count = True
            if should_count:
                if r_type in ["إيراد", "تحويل وارد"]: balance += r_amount
                elif r_type in ["مصروف", "تحويل صادر", "تحويل خارجي"]: balance -= r_amount
        except: pass
    return balance

def save_control_to_sheet_logic():
    add_log("💾 جاري حفظ القاموس...", "blue")
    try:
        # --- تعديل للمسار الذكي ---
        json_path = resource_path("credentials.json")
        
        scope = ["https://spreadsheets.google.com/feeds", "https://www.googleapis.com/auth/drive"]
        creds = ServiceAccountCredentials.from_json_keyfile_name(json_path, scope)
        client = gspread.authorize(creds)
        ws = client.open("Masrofat").worksheet("Control")
        new_rows = [["Keyword", "Mapped_Value", "Type"]]
        for ctrl in control_list_view.controls:
            row_content = ctrl.content.controls
            kw = row_content[0].value
            mv = row_content[1].value
            display_tp = row_content[2].value
            real_tp = get_type_code(display_tp)
            if kw: new_rows.append([kw, mv, real_tp])
        ws.clear() 
        ws.update('A1', new_rows)
        threading.Thread(target=load_data_background, daemon=True).start()
        speak("تم حفظ التعديلات")
    except Exception as ex:
        add_log(f"❌ خطأ في الحفظ: {ex}", "red")
        speak("حدث خطأ أثناء حفظ القاموس")

# ---------------------------------------------------------
# 3. الاتصال بقاعدة البيانات
# ---------------------------------------------------------
def check_internet():
    try:
        socket.create_connection(("8.8.8.8", 53), timeout=3)
        return True
    except OSError:
        return False

def save_offline_transaction(row_data):
    try:
        csv_path = resource_path("offline_trans.csv")
        with open(csv_path, mode='a', newline='', encoding='utf-8') as file:
            writer = csv.writer(file)
            writer.writerow(row_data)
        add_log("💾 تم حفظ العملية محلياً (أوفلاين)", "orange")
    except Exception as e:
        add_log(f"❌ خطأ في الحفظ المحلي: {e}", "red")

def load_data_background():
    if app_state["is_loading"]: return 
    app_state["is_loading"] = True
    
    global raw_data, config_data, control_dict, PAYMENT_OPTS

    app_state["header_text"] = "📡 1/5 التحقق من الإنترنت..."
    app_state["header_color"] = "orange"
    
    if not check_internet():
        app_state["is_offline"] = True
        app_state["header_text"] = "⚠️ وضع الأوفلاين مفعل"
        app_state["header_color"] = "red"
        add_log("❌ لا يوجد إنترنت، جاري تحميل البيانات المحفوظة...", "orange")
        speak("لا يوجد اتصال بالإنترنتْ، تم تفعيل وضع الأوفلاينْ")
        
        # --- تحميل البيانات من الذاكرة المحلية (الكاش) للعمل أوفلاين ---
        cache_path = resource_path("local_cache.json")
        if os.path.exists(cache_path):
            try:
                with open(cache_path, 'r', encoding='utf-8') as f:
                    cached = json.load(f)
                    raw_data = cached.get("raw_data", [])
                    config_data = cached.get("config_data", [])
                    raw_control = cached.get("raw_control", [])
                    
                    temp_payment_opts = {}
                    for row in config_data:
                        if len(row) >= 5:
                            entity = row[0].strip()
                            pay_method = row[4].strip()
                            if entity:
                                if entity not in temp_payment_opts: temp_payment_opts[entity] = []
                                if pay_method and pay_method not in temp_payment_opts[entity]: temp_payment_opts[entity].append(pay_method)
                    PAYMENT_OPTS = temp_payment_opts
                    
                    control_dict["synonyms"].clear(); control_dict["nav"].clear(); control_dict["defaults"].clear()
                    for row in raw_control:
                        if len(row) >= 3:
                            keyword = row[0].strip().lower()
                            mapped_val = row[1].strip()
                            c_type = row[2].strip()
                            if c_type == "Entity" or c_type == "Trans_Type": control_dict["synonyms"][keyword] = mapped_val
                            elif c_type == "Nav": control_dict["nav"][keyword] = mapped_val
                            elif c_type == "Payment": control_dict["defaults"][keyword] = mapped_val
                            
                app_state["data_ready"] = True
                add_log("✅ تم تحميل القوائم للعمل أوفلاين بنجاح", "green")
            except Exception as e:
                add_log(f"❌ خطأ في قراءة الملف المحلي: {e}", "red")
        else:
            add_log("⚠️ لا توجد بيانات سابقة محفوظة، القوائم ستكون فارغة", "red")
            
        app_state["is_loading"] = False
        return

    try:
        app_state["header_text"] = "🔐 2/5 جاري المصادقة..."
        json_path = resource_path("credentials.json")
        
        if not os.path.exists(json_path):
            raise FileNotFoundError(f"ملف المصادقة غير موجود: {json_path}")

        scope = ["https://spreadsheets.google.com/feeds", "https://www.googleapis.com/auth/drive"]
        creds = ServiceAccountCredentials.from_json_keyfile_name(json_path, scope)
        client = gspread.authorize(creds)
        
        app_state["header_text"] = "📂 3/5 فتح جداول البيانات..."
        
        conf_path = resource_path("app_config.json")
        sheet_url = "Masrofat"
        if os.path.exists(conf_path):
            with open(conf_path, 'r') as f:
                sheet_url = decode_base64(json.load(f).get("sheet_url", encode_base64("Masrofat")))
        
        spreadsheet = client.open_by_url(sheet_url) if "http" in sheet_url else client.open(sheet_url)
        
        app_state["header_text"] = "📥 4/5 سحب العمليات والإعدادات..."
        
        sheet_config = spreadsheet.worksheet("Data")
        sheet_main = spreadsheet.sheet1
        
        try:
            sheet_control = spreadsheet.worksheet("Control")
            raw_control = sheet_control.get_all_values()[1:] 
        except:
            raw_control = []

        new_raw_data = sheet_main.get_all_values()[1:] 
        new_config_data = sheet_config.get_all_values()[1:] 
        
        app_state["header_text"] = "🧠 5/5 معالجة وربط البيانات..."
        
        raw_data = new_raw_data
        config_data = new_config_data
        
        # --- حفظ نسخة محلية (كاش) للعمل بها وقت الأوفلاين لاحقاً ---
        try:
            cache_path = resource_path("local_cache.json")
            with open(cache_path, 'w', encoding='utf-8') as f:
                json.dump({"raw_data": raw_data, "config_data": config_data, "raw_control": raw_control}, f, ensure_ascii=False)
        except: pass
        
        temp_payment_opts = {}
        for row in config_data:
            if len(row) >= 5:
                entity = row[0].strip()
                pay_method = row[4].strip()
                if entity:
                    if entity not in temp_payment_opts: temp_payment_opts[entity] = []
                    if pay_method and pay_method not in temp_payment_opts[entity]: temp_payment_opts[entity].append(pay_method)
        PAYMENT_OPTS = temp_payment_opts
        
        control_dict["synonyms"].clear(); control_dict["nav"].clear(); control_dict["defaults"].clear()
        for row in raw_control:
            if len(row) >= 3:
                keyword = row[0].strip().lower()
                mapped_val = row[1].strip()
                c_type = row[2].strip()
                if c_type == "Entity" or c_type == "Trans_Type": control_dict["synonyms"][keyword] = mapped_val
                elif c_type == "Nav": control_dict["nav"][keyword] = mapped_val
                elif c_type == "Payment": control_dict["defaults"][keyword] = mapped_val

        app_state["data_ready"] = True
        app_state["header_text"] = "✅ تم الاتصال بالسيرفر بنجاح"
        app_state["header_color"] = "green"
        add_log(f"✅ تم تحديث البيانات ({len(raw_data)} عملية)", "green")
        
    except Exception as e:
        app_state["header_text"] = "❌ خطأ في الاتصال"
        app_state["header_color"] = "red"
        add_log(f"❌ فشل الاتصال: {str(e)}", "red")
        speak("توجد مشكه في الاتصال بالإنترنتْ")
    
    finally:
        app_state["is_loading"] = False
        

def listen_background():
    # تم إيقاف الاستماع في الخلفية مؤقتاً لتجنب الكراش على الموبايل
    # سيتم الاعتماد على مايك الكيبورد لاحقاً
    while True:
        time.sleep(1)

def handle_silence_logic():
    app_state["silence_counter"] += 1
    count = app_state["silence_counter"]
    if count >= 3:
        app_state["mic_status"] = "idle"
        app_state["header_text"] = "💤 وضع الخمول"; app_state["header_color"] = "grey"
        add_log("💤 لا يوجد توجيه واضح.. سأنتظر", "grey")
        speak("يبدو أن الأمر لا يخصَنيْ") 
        app_state["silence_counter"] = 0
    else:
        app_state["header_text"] = f"⚠️ مسمعتش ({count}/3).."; app_state["header_color"] = "grey"
        speak("لم أسمع بوضوحْ")
        time.sleep(0.5)
        app_state["mic_status"] = "listening"

def trigger_listening_mode():
    speak("أنا أسمَعكْ") 
    app_state["header_text"] = "🎙️ سامعك.. اتفضل"
    app_state["header_color"] = "red"
    app_state["mic_status"] = "listening"
    app_state["silence_counter"] = 0

def smart_parser(text):
    current_page = app_state["current_page"]
    result = {"intent": "unknown", "data": {}}

    if any(w in text for w in ["اسكت", "إسكت", "اقفل ودنك", "مش ليك", "الكلام مش ليك"]):
        return {"intent": "stop_listening", "data": {}}

    if any(w in text for w in ["إلغاء", "الغاء", "كنسل", "خلاص", "تمام", "ماشي", "احفظ", "سجل", "حفظ"]):
        if any(w in text for w in ["احفظ", "سجل", "تمام", "حفظ", "ماشي"]):
             if app_state["is_dialog_open"]: return {"intent": "close_dialog", "data": {}}
             if current_page == "reg": return {"intent": "save_transaction", "data": {}}
        return {"intent": "cancel", "data": {}}

    for kw, val in control_dict.get("nav", {}).items():
        if kw in text or fuzzy_match(kw, text.split(), cutoff=0.85): 
             return {"intent": "navigate", "data": val}

    if current_page == "cash": return parse_cash_command(text)
    elif current_page == "bal": return parse_balance_command(text)
    elif current_page == "reg": return parse_register_command(text)
    
    return result

def parse_cash_command(text):
    denoms = [200, 100, 50, 20, 10, 5, 1, 0.5]
    all_safes = set()
    for v in PAYMENT_OPTS.values(): all_safes.update(v)
    for r in raw_data: 
        if len(r)>6 and r[6]: all_safes.add(r[6])
    
    matched_safe = fuzzy_match(text, list(all_safes), cutoff=0.5)
    if matched_safe: return {"intent": "select_safe", "data": matched_safe}

    ordinal_map = {
        "أول": 0, "اول": 0, "الاول": 0, "لأول": 0,
        "تاني": 1, "ثاني": 1, "الثاني": 1, "التاني": 1,
        "تالت": 2, "ثالث": 2, "الثالث": 2, "التالت": 2,
        "رابع": 3, "الرابع": 3, "خامس": 4, "الخامس": 4,
        "سادس": 5, "السادس": 5, "سابع": 6, "السابع": 6,
        "ثامن": 7, "تامن": 7, "الثامن": 7, "اخير": 7
    }
    
    found_denom = None
    for word, idx in ordinal_map.items():
        if word in text and idx < len(denoms):
            found_denom = denoms[idx]
            break
            
    if found_denom is None:
        denoms_map = {"200": 200, "متينات": 200, "ميتين": 200, "متين": 200, "100": 100, "ميات": 100, "مية": 100, "50": 50, "خمسين": 50, "خمسينات": 50, "20": 20, "عشرين": 20, "عشرينات": 20, "10": 10, "عشرة": 10, "عشرات": 10, "5": 5, "خمسة": 5, "خمسات": 5, "1": 1, "جنيه": 1, "فكة": 1, "انصاص": 0.5, "نص": 0.5}
        for word, val in denoms_map.items():
            if word in text: found_denom = val; break
    
    if found_denom is not None:
        nums = re.findall(r'\d+', text)
        count = 0
        if nums:
            for n in nums:
                if float(n) != found_denom: count = int(n); break
            if count == 0 and len(nums) > 0: count = int(nums[0])
        
        if count == 0:
            words = text.split()
            for w in words:
                w_norm = normalize_word(w)
                if w_norm in TEXT_TO_NUM:
                    count = TEXT_TO_NUM[w_norm]
                    break
        
        return {"intent": "update_cash", "data": {"denom": found_denom, "count": count}}

    return {"intent": "unknown", "data": {}}

def parse_balance_command(text):
    if "تفاصيل" in text or "وريني" in text:
        ents = list(PAYMENT_OPTS.keys())
        for r in raw_data:
            if len(r) > 5 and r[5]: ents.append(r[5])
        ents = list(set(ents))

        target = fuzzy_match(text, ents, cutoff=0.5) 
        if not target:
             words = text.split()
             for w in words:
                 if w in control_dict["synonyms"]:
                     mapped = control_dict["synonyms"][w]
                     if mapped in ents: target = mapped; break
        if target: return {"intent": "show_details", "data": target}
    return {"intent": "unknown", "data": {}}

def search_in_config(text):
    if not text or not config_data: return None
    words = clean_text(text).split()
    for word in words:
        word_norm = normalize_word(word)
        if len(word_norm) < 3: continue 
        for row in config_data:
            if len(row) < 3: continue
            entity, main, sub = row[0].strip(), row[1].strip(), row[2].strip()
            if not sub: continue
            sub_norm = normalize_word(sub)
            if word_norm in sub_norm or sub_norm in word_norm:
                return {"entity": entity, "main": main, "sub": sub}
            if difflib.get_close_matches(word_norm, [sub_norm], n=1, cutoff=0.45):
                 return {"entity": entity, "main": main, "sub": sub}
    return None

def parse_register_command(text):
    if any(w in text for w in ["احفظ", "سجل", "تمام"]):
        return {"intent": "save_transaction", "data": {}}

    result = {"intent": "fill_form", "data": {"amount": None, "details": "", "entity": None, "main": None, "sub": None, "payment": None, "type": "مصروف"}}
    
    amount_match = re.search(r'(\d+)', text)
    if amount_match:
        result["data"]["amount"] = amount_match.group(1)
        text_without_amount = text.replace(result["data"]["amount"], "")
        result["data"]["details"] = clean_text(text_without_amount)
    else:
        result["data"]["details"] = clean_text(text)

    search_key = result["data"]["details"]
    found_in_history = False
    found_in_config = False

    if search_key:
        for row in reversed(raw_data):
            if len(row) < 9: continue
            hist_details = row[2].strip() if row[2] else ""
            hist_sub = row[4].strip() if row[4] else ""
            sk_norm = normalize_word(search_key)
            hd_norm = normalize_word(hist_details)
            hs_norm = normalize_word(hist_sub)
            if sk_norm in hd_norm or sk_norm in hs_norm:
                result["data"]["entity"] = row[5].strip()
                result["data"]["main"] = row[3].strip()
                result["data"]["sub"] = row[4].strip()
                result["data"]["type"] = row[8].strip()
                found_in_history = True
                break
    
    if not found_in_history and search_key:
        config_res = search_in_config(text) 
        if config_res:
            result["data"]["entity"] = config_res["entity"]
            result["data"]["main"] = config_res["main"]
            result["data"]["sub"] = config_res["sub"]
            found_in_config = True

    if not found_in_history and not found_in_config:
        words = text.split()
        all_entities = list(PAYMENT_OPTS.keys())
        for w in words:
            if not result["data"]["entity"]:
                matched_entity = fuzzy_match(w, all_entities, cutoff=0.8)
                if matched_entity: result["data"]["entity"] = matched_entity

        if result["data"]["entity"]:
            selected_entity = result["data"]["entity"]
            available_mains = sorted(list(set([row[1].strip() for row in config_data if len(row) > 1 and row[0].strip() == selected_entity and row[1]])))
            for w in words:
                 matched_main = fuzzy_match(w, available_mains, cutoff=0.6)
                 if matched_main: result["data"]["main"] = matched_main; break

    if not result["data"]["payment"]:
        result["data"]["payment"] = f"عهدة {app_state['user_name']}"

    if not found_in_history and not found_in_config and not result["data"]["entity"] and search_key:
        return {"intent": "new_category_error", "data": {}}

    return result

# ---------------------------------------------------------
# 5. واجهة المستخدم (Main Function)
# ---------------------------------------------------------

# تعريف الدوال هنا لتكون مرئية لـ main
def get_type_code(arabic_val):
    mapping = {"كيان (مصدر)": "Entity", "نوع عملية": "Trans_Type", "تنقل (شاشات)": "Nav", "دفع افتراضي": "Payment"}
    return mapping.get(arabic_val, "Entity")

def get_type_display(code_val):
    mapping = {"Entity": "كيان (مصدر)", "Trans_Type": "نوع عملية", "Nav": "تنقل (شاشات)", "Payment": "دفع افتراضي"}
    return mapping.get(code_val, code_val)

def remove_dict_row(row_ctrl):
    if row_ctrl in control_list_view.controls:
        control_list_view.controls.remove(row_ctrl)
        try: control_list_view.update()
        except: pass

def add_dictionary_row(kw="", mv="", tp="Entity"):
    row = ft.Container(
        content=ft.Row([
            ft.TextField(value=kw, hint_text="الكلمة", width=110, height=40, text_size=12, bgcolor="white", content_padding=5, text_align="center"),
            ft.TextField(value=mv, hint_text="المعنى", width=110, height=40, text_size=12, bgcolor="white", content_padding=5, text_align="center"),
            ft.Dropdown(
                value=get_type_display(tp), 
                options=[ft.dropdown.Option("كيان (مصدر)"), ft.dropdown.Option("نوع عملية"), ft.dropdown.Option("تنقل (شاشات)"), ft.dropdown.Option("دفع افتراضي")],
                width=120, height=40, text_size=11, content_padding=5, bgcolor="white"
            ),
            ft.IconButton( ft.icons.DELETE_OUTLINE, icon_color="red", on_click=lambda e: remove_dict_row(e.control.parent.parent))
        ], alignment=ft.MainAxisAlignment.CENTER, spacing=5),
        padding=2, border=ft.border.only(bottom=ft.border.BorderSide(1, "#eee"))
    )
    control_list_view.controls.append(row)
    try: control_list_view.update()
    except: pass

def main_app(page: ft.Page):

# تعريف أداة تشغيل الصوت
    audio_player = ft.Audio(src="https://www.soundjay.com/buttons/beep-01a.mp3", volume=0, autoplay=False)

    page.overlay.append(audio_player)

    def local_speak(text):
        # 1. تحديث شاشة الترجمة فوراً (تشتغل حتى لو مفيش نت)
        rico_subtitle.value = text
        rico_subtitle.visible = True
        try:
            rico_subtitle.update()
        except:
            pass

        # 2. لو إحنا في وضع الأوفلاين، نكتفي بالنص المكتوب ومنحاولش نكلم السيرفر
        if app_state.get("is_offline", False):
            return

        # 3. جلب الصوت من جوجل وتشغيله من الرامات مباشرة
        def _speak_logic():
            try:
                import requests
                GOOGLE_API_KEY = "AIzaSyCIInYyWdwnTzzCDvwiZb4OuvHcXAKcX5g" # مفتاحك المجاني (4 مليون حرف)
                url = f"https://texttospeech.googleapis.com/v1/text:synthesize?key={GOOGLE_API_KEY}"
                payload = {
                    "input": {"text": text},
                    "voice": {"languageCode": "ar-XA", "name": "ar-XA-Wavenet-B"},
                    "audioConfig": {
                        "audioEncoding": "MP3",
                        "speakingRate": 1.2
                    }
                }

                # طلب الصوت من السيرفر
                response = requests.post(url, json=payload, timeout=10)

                if response.status_code == 200:
                    import time
                    audio_content = response.json()['audioContent']
                    audio_player.src_base64 = audio_content
                    audio_player.volume = 1  # 🔊 هنا رجعنا الصوت لأعلى حاجة
                    audio_player.update()
                    time.sleep(0.1)  # إعطاء البرنامج جزء من الثانية لاستيعاب الملف
                    audio_player.play()
                
                elif response.status_code == 403:
                    # لو الـ 4 مليون حرف خلصوا، البرنامج مش هيضرب إيرور أحمر، هيكتب بس للمستخدم!
                    rico_subtitle.value = f"{text} (عذراً، باقة الصوت انتهت لهذا الشهر)"
                    try: rico_subtitle.update()
                    except: pass
                    add_log("⚠️ باقة API جوجل انتهت لهذا الشهر (403) - تم التحويل للنص فقط", "orange")
                
                else:
                    add_log(f"⚠️ خطأ من سيرفر جوجل: {response.status_code}", "orange")

            except Exception as e:
                add_log(f"⚠️ خطأ في الاتصال بالصوت: {e}", "red")

        import threading
        threading.Thread(target=_speak_logic, daemon=True).start()

    global global_speak_bridge
    global_speak_bridge = local_speak

    # --- [ منطق الألة الحاسبه المضاف والمعدل ] ---
    # --- [ منطق الألة الحاسبه المضاف والمعدل ] ---
    def get_current_value(dd_control, txt_control):
        if txt_control.visible and txt_control.value: return txt_control.value
        return dd_control.value

    def calc_general_submit(e):
        try:
            if any(op in e.control.value for op in "+-*/"):
                formula = e.control.value
                result = eval(formula)
                final_res = round(result, 2)
                e.control.value = str(final_res)
                
                sub_val = get_current_value(dd_sub, txt_sub)
                if sub_val:
                    txt_details.value = f"حساب: {formula} : {sub_val}"
                else:
                    txt_details.value = f"حساب: {formula}"
                
                txt_details.update()
                e.control.update()
                txt_details.focus()
        except Exception as ex:
            add_log(f"⚠️ خطأ في الحساب: {ex}", "red")

    def calc_cash_submit(e):
        try:
            val = e.control.value
            if "*" in val or "/" in val:
                e.control.error_text = "جمع وطرح فقط!"
                e.control.update()
                return
            if "+" in val or "-" in val:
                result = eval(val)
                if "0.5" in val or "0.5" in str(result):
                     e.control.value = str(result)
                else:
                     e.control.value = str(int(result))
                e.control.error_text = None
                e.control.update()
                calc_cash_logic(e)
        except:
            e.control.error_text = "خطأ"
            e.control.update()
    # ---------------------------------------

    page.title = "Reco Pro V-1.1"
    page.rtl = True
    page.bgcolor = "#f0f2f5"
    page.window_width = 410
    page.window_height = 800
    page.theme_mode = ft.ThemeMode.LIGHT
    page.horizontal_alignment = ft.CrossAxisAlignment.CENTER
    page.padding = 5 
    page.floating_action_button = ft.FloatingActionButton(
        icon= ft.icons.MIC,
        bgcolor="#E91E63",
        visible=False,
        on_click=lambda e: manual_mic_click(e)
    )
    
    # --- Date Logic Implementation (Clean Look) ---
    today = datetime.now()
    lbl_day_name = ft.Text("", weight="bold", color="blue", size=14)
    
    # 3 Fields for Date (Frameless & Transparent)

    txt_custom_day = ft.TextField(value=str(today.day), width=40, text_align="center", text_size=14, border_color="transparent", focused_border_color="transparent", keyboard_type=ft.KeyboardType.NUMBER, bgcolor="transparent")
    txt_custom_month = ft.TextField(value=str(today.month), width=40, text_align="center", text_size=14, border_color="transparent", focused_border_color="transparent", keyboard_type=ft.KeyboardType.NUMBER, bgcolor="transparent")
    txt_custom_year = ft.TextField(value=str(today.year), width=60, text_align="center", text_size=14, border_color="transparent", focused_border_color="transparent", keyboard_type=ft.KeyboardType.NUMBER, bgcolor="transparent")


    # Clean wrapper (No border)
    def create_date_field(ctrl):
        return ft.Container(content=ctrl, padding=0)

    def validate_custom_date(e=None):
        for ctrl in [txt_custom_day, txt_custom_month, txt_custom_year]:
            if not ctrl.value.isdigit() and ctrl.value != "":
                ctrl.value = "".join(filter(str.isdigit, ctrl.value))
                ctrl.update()
        
        d_val, m_val, y_val = txt_custom_day.value, txt_custom_month.value, txt_custom_year.value
        
        if not d_val or not m_val or not y_val: 
            lbl_day_name.value = "..."
            lbl_day_name.update()
            return

        try:
            d, m, y = int(d_val), int(m_val), int(y_val)
            if len(y_val) == 4:
                if y < 2000: y = 2000; txt_custom_year.value = "2000"; txt_custom_year.update()
                if y > 3000: y = 3000; txt_custom_year.value = "3000"; txt_custom_year.update()
            if m < 1: m = 1; txt_custom_month.value = "1"; txt_custom_month.update()
            if m > 12: m = 12; txt_custom_month.value = "12"; txt_custom_month.update()
            max_days = 31
            if m in [4, 6, 9, 11]: max_days = 30
            elif m == 2:
                if (y % 4 == 0 and y % 100 != 0) or (y % 400 == 0): max_days = 29
                else: max_days = 28
            if d < 1: d = 1; txt_custom_day.value = "1"; txt_custom_day.update()
            if d > max_days: d = max_days; txt_custom_day.value = str(max_days); txt_custom_day.update()

            if len(y_val) == 4:
                date_obj = datetime(y, m, d)
                day_eng = date_obj.strftime("%A")
                lbl_day_name.value = ARABIC_DAYS.get(day_eng, day_eng)
                lbl_day_name.update()
        except: pass

    txt_custom_day.on_change = validate_custom_date
    txt_custom_month.on_change = validate_custom_date
    txt_custom_year.on_change = validate_custom_date
    validate_custom_date()

    row_custom_date = ft.Row(
        [
            lbl_day_name,
            ft.Container(width=10), 
            create_date_field(txt_custom_day),
            ft.Text("/", size=16, color="black", weight="bold"),
            create_date_field(txt_custom_month),
            ft.Text("/", size=16, color="black", weight="bold"),
            create_date_field(txt_custom_year),
        ],
        alignment=ft.MainAxisAlignment.CENTER,
        spacing=0
    )

    btn_sync = ft.ElevatedButton("🔄 مزامنة العمليات المعلقة", bgcolor="orange", color="white", visible=False)
    
    def check_sync_status():
        csv_path = resource_path("offline_trans.csv")
        if os.path.exists(csv_path) and os.path.getsize(csv_path) > 0 and not app_state.get("is_offline", False):
            btn_sync.visible = True
        else:
            btn_sync.visible = False
        try: btn_sync.update()
        except: pass

    def perform_sync(e=None):
        csv_path = resource_path("offline_trans.csv")
        if not os.path.exists(csv_path): return
        btn_sync.text = "جاري المزامنة..."; btn_sync.disabled = True
        try: btn_sync.update()
        except: pass

        try:
            json_path = resource_path("credentials.json")
            scope = ["https://spreadsheets.google.com/feeds", "https://www.googleapis.com/auth/drive"]
            creds = ServiceAccountCredentials.from_json_keyfile_name(json_path, scope)
            client = gspread.authorize(creds)
            
            sheet_url = "Masrofat"
            conf_path = resource_path("app_config.json")
            if os.path.exists(conf_path):
                with open(conf_path, 'r') as f:
                    sheet_url = decode_base64(json.load(f).get("sheet_url", encode_base64("Masrofat")))
            
            s_main = client.open_by_url(sheet_url).sheet1 if "http" in sheet_url else client.open(sheet_url).sheet1
            
            rows_to_sync = []
            with open(csv_path, mode='r', encoding='utf-8') as file:
                reader = csv.reader(file)
                for row in reader:
                    if row: rows_to_sync.append(row)
            
            if rows_to_sync: s_main.append_rows(rows_to_sync)
            open(csv_path, 'w').close()
            add_log("✅ تمت مزامنة العمليات بنجاح", "green")#; speak("تمت المزامنة")
            trigger_refresh_thread()
        except Exception as ex:
            add_log(f"❌ فشل المزامنة: {ex}", "red")
        finally:
            btn_sync.text = "🔄 مزامنة العمليات المعلقة"; btn_sync.disabled = False; check_sync_status(); update_offline_counter_ui()
    btn_sync.on_click = perform_sync

    # --- Strict Date Input (Reports - Explicitly Defined BEFORE use) ---
    def validate_report_date(e=None):
        try:
            for ctrl in [rep_txt_day, rep_txt_month, rep_txt_year]:
                if not ctrl.value.isdigit() and ctrl.value != "":
                    ctrl.value = "".join(filter(str.isdigit, ctrl.value))
                    ctrl.update()
        except: pass

    rep_txt_day = ft.TextField(hint_text="DD", width=40, text_align="center", max_length=2, border=ft.InputBorder.UNDERLINE, bgcolor="white", text_size=12, on_change=validate_report_date)
    rep_txt_month = ft.TextField(hint_text="MM", width=40, text_align="center", max_length=2, border=ft.InputBorder.UNDERLINE, bgcolor="white", text_size=12, on_change=validate_report_date)
    rep_txt_year = ft.TextField(hint_text="YYYY", width=60, text_align="center", max_length=4, border=ft.InputBorder.UNDERLINE, bgcolor="white", text_size=12, on_change=validate_report_date)
    
    date_input_row = ft.Row([rep_txt_day, ft.Text("/", size=16, color="grey"), rep_txt_month, ft.Text("/", size=16, color="grey"), rep_txt_year], alignment=ft.MainAxisAlignment.CENTER, visible=False)    # -------------------------------------------------------------------

    # --- Dialogs ---
    def close_dlg(e):
        dlg_modal.open = False
        app_state["row_to_delete"] = None
        page.update()

    def confirm_dlg(e):
        dlg_modal.open = False
        page.update()
        if app_state["row_to_delete"]:
            delete_transaction_logic(app_state["row_to_delete"])
            app_state["row_to_delete"] = None

    dlg_text = ft.Text("هل أنت متأكد؟")
    dlg_modal = ft.AlertDialog(modal=True, title=ft.Text("تأكيد الحذف ⚠️"), content=dlg_text, actions=[ft.TextButton("نعم، احذف", on_click=confirm_dlg, style=ft.ButtonStyle(color="red")), ft.TextButton("لا، إلغاء", on_click=close_dlg)], actions_alignment=ft.MainAxisAlignment.END)
    page.overlay.append(dlg_modal) 

    # --- Choice Dialog ---
    def close_choice_dlg(e):
        dlg_choice.open = False
        app_state["is_dialog_open"] = False
        page.update()

    def on_choice_click(e):
        selected = e.control.data
        dlg_choice.open = False
        app_state["is_dialog_open"] = False
        
        if app_state["current_rep_target"] == "cash":
            btn_select_safe.text = selected
            btn_select_safe.update()
            on_safe_changed(selected)
        elif app_state["current_rep_target"] == "rep_entity":
            rep_state["entity"] = selected
            btn_rep_entity.content.value = f"الكيان: {selected}"
            btn_rep_entity.update()
            update_report_view()
        elif app_state["current_rep_target"] == "rep_period":
            rep_state["period"] = selected
            btn_rep_period.content.value = f"الفترة: {selected}"
            btn_rep_period.update()
            update_report_view()
        elif app_state["current_rep_target"] == "rep_main":
            rep_state["main"] = selected
            rep_state["sub"] = "الكل" 
            btn_rep_sub.content.value = "فرعي: الكل"
            if selected != "الكل":
                btn_rep_sub.disabled = False; btn_rep_sub.bgcolor = "white"
            else:
                btn_rep_sub.disabled = True; btn_rep_sub.bgcolor = "#eeeeee"
            btn_rep_main.content.value = f"رئيسي: {selected}"
            btn_rep_main.update()
            btn_rep_sub.update()
            update_report_view()
        elif app_state["current_rep_target"] == "rep_sub":
            rep_state["sub"] = selected
            btn_rep_sub.content.value = f"فرعي: {selected}"
            btn_rep_sub.update()
            update_report_view()
        page.update()

    choice_list = ft.ListView(expand=True, spacing=10)
    dlg_choice = ft.AlertDialog(title=ft.Text("اختر..."), content=ft.Container(content=choice_list, width=300, height=400), actions=[ft.TextButton("إلغاء", on_click=close_choice_dlg)])
    page.overlay.append(dlg_choice)

    # --- Drill Down Popup ---
    def close_box_dlg(e=None):
        dlg_box_details.open = False
        app_state["is_dialog_open"] = False
        page.update()

    dlg_box_content = ft.ListView(expand=True, spacing=10, padding=10)
    dlg_box_details = ft.AlertDialog(title=ft.Text("تفاصيل الرصيد"), content=ft.Container(content=dlg_box_content, width=300, height=300, bgcolor="white", border_radius=10), actions=[ft.TextButton("إغلاق", on_click=close_box_dlg)])
    page.overlay.append(dlg_box_details)

    def on_box_click(e):
        data = e.control.data
        name = data['name']
        total = data['total']
        breakdown = data['breakdown']
        dlg_box_details.title.value = f"تفاصيل: {name}"
        dlg_box_content.controls.clear()
        dlg_box_content.controls.append(ft.Container(content=ft.Column([ft.Text("الإجمالي الكلي", size=12, color="grey"), ft.Text(f"{total:,.0f}", size=24, weight="bold", color="blue")], horizontal_alignment="center"), alignment=ft.Alignment(0, 0), padding=10))
        dlg_box_content.controls.append(ft.Divider())
        for k, v in breakdown.items():
            if v == 0: continue
            dlg_box_content.controls.append(ft.ListTile(leading=ft.Icon( ft.icons.SUBDIRECTORY_ARROW_RIGHT, color="green"), title=ft.Text(k, weight="bold", size=12), trailing=ft.Text(f"{v:,.0f}", weight="bold", color="black", size=12)))
        dlg_box_details.open = True
        app_state["is_dialog_open"] = True
        page.update()

    # --- شاشة الترجمة (Subtitles) ---
    rico_subtitle = ft.Text("", size=15, color="#1565C0", weight="bold", text_align=ft.TextAlign.CENTER, visible=False)

    # --- Smart Audio Visualizer (Single Bar Style) ---
    volume_bar = ft.Container(
        width=0, 
        height=10, 
        bgcolor="#E91E63", 
        border_radius=5, 
        animate=ft.Animation(100, "easeOut")
    )
    
    # Correct alignment using numerical values
    audio_visualizer_container = ft.Container(
        content=volume_bar,
        width=300, 
        height=10, 
        bgcolor="#e0e0e0", 
        border_radius=5, 
        alignment=ft.Alignment(-1, 0)
    )

    audio_bottom_bar = ft.Container(
        content=audio_visualizer_container,
        bgcolor="#f0f2f5", 
        padding=10,
        alignment=ft.Alignment(0, 0)
    )

    header_txt = ft.Text("🚀 جاري بدء النظام...", size=18, weight="bold", color="orange")
    timer_lbl = ft.Text("⏱️ 00:00:00", size=14, color="grey")

    # --- سحر الأوفلاين التفاعلي (العداد والرسائل) ---
    offline_count_txt = ft.Text("", size=13, color="red", weight="bold", visible=False)

    def get_offline_count():
        try:
            p = resource_path("offline_trans.csv")
            if not os.path.exists(p): return 0
            with open(p, 'r', encoding='utf-8') as f: return sum(1 for row in csv.reader(f) if row)
        except: return 0

    def update_offline_counter_ui():
        c = get_offline_count()
        if app_state.get("is_offline") and c > 0:
            offline_count_txt.value = f"⚠️ يوجد ({c}) عمليات محفوظة أوفلاين بانتظار الإنترنت"
            offline_count_txt.visible = True
        else: offline_count_txt.visible = False
        try: offline_count_txt.update()
        except: pass

    def open_delete_confirm(e):
        dlg_offline_action.open = False
        dlg_offline_confirm_delete.content.value = f"سيتم حذف ({get_offline_count()}) عملية نهائياً.\nهل أنت متأكد؟"
        dlg_offline_confirm_delete.open = True; page.update()

    def confirm_offline_delete(e):
        open(resource_path("offline_trans.csv"), 'w').close()
        dlg_offline_confirm_delete.open = False; update_offline_counter_ui(); check_sync_status()
        add_log("🗑️ تم حذف العمليات الأوفلاين نهائياً", "red"); page.update()

    dlg_offline_action = ft.AlertDialog(modal=True, title=ft.Text("مزامنة الأوفلاين 🔄"), content=ft.Text(""), actions=[ft.TextButton("رفع الآن للشيت", on_click=lambda e: [setattr(dlg_offline_action, 'open', False), page.update(), perform_sync(e)], style=ft.ButtonStyle(color="green")), ft.TextButton("ليس الآن", on_click=lambda e: [setattr(dlg_offline_action, 'open', False), page.update()]), ft.TextButton("حذفها نهائياً", on_click=open_delete_confirm, style=ft.ButtonStyle(color="red"))], actions_alignment=ft.MainAxisAlignment.SPACE_BETWEEN)
    dlg_offline_confirm_delete = ft.AlertDialog(modal=True, title=ft.Text("تأكيد الحذف ⚠️", color="red"), content=ft.Text(""), actions=[ft.TextButton("نعم، احذف نهائياً", on_click=confirm_offline_delete, style=ft.ButtonStyle(color="red")), ft.TextButton("إلغاء", on_click=lambda e: [setattr(dlg_offline_confirm_delete, 'open', False), page.update()])], actions_alignment=ft.MainAxisAlignment.END)
    page.overlay.extend([dlg_offline_action, dlg_offline_confirm_delete])
    # ------------------------------------------------    

    cancel_btn = ft.ElevatedButton(content=ft.Text("X", color="white", weight="bold"), bgcolor="grey", width=50, height=45, disabled=True, tooltip="إلغاء")
    
    save_btn = ft.ElevatedButton("حفظ العملية", on_click=lambda e: save_data(e), bgcolor="#2E7D32", color="white", width=250, height=45, disabled=True)

    def enable_cancel_btn(e=None):
        if cancel_btn.disabled:
            cancel_btn.disabled = False; cancel_btn.bgcolor = "red"; cancel_btn.update()
        if save_btn.disabled:
            save_btn.disabled = False; save_btn.update()

# --- ودان ريكو الجديدة (مايك الكيبورد الذكي) ---
    app_state["voice_timer"] = None

# --- ودان ريكو الجديدة (مايك الكيبورد الذكي) ---
    app_state["voice_timer"] = None

    def process_voice_command(e=None):
        cmd_text = voice_input_field.value.strip()
        voice_dialog.open = False
        try: page.update()
        except: pass
        
        if cmd_text:
            add_log(f"🗣️ أمر: {cmd_text}", "blue")
            app_state["last_command"] = cmd_text
            
            parsed = smart_parser(cmd_text)
            intent = parsed["intent"]
            data = parsed["data"]
            
            if intent == "navigate":
                nav_click(type("", (), {"control": type("", (), {"data": data})()})())
                speak("هذهِ هيَ")
            elif intent == "fill_form":
                if data["amount"]: txt_amount.value = data["amount"]; txt_amount.update()
                if data["details"]: txt_details.value = data["details"]; txt_details.update()
                add_log("✅ تم تنفيذ الأمر", "green")
                speak(f"تمامْ.. {data['amount'] if data['amount'] else ''} {data['details']}")
            elif intent == "save_transaction":
                save_data()
            elif intent == "cancel" or intent == "stop_listening":
                cancel_operation()
                speak("تمامْ، لغيتْ الأمرْ")
            else:
                if len(cmd_text.strip()) > 4:
                    add_log("⚠️ لم أفهم الأمرْ", "orange")
                    speak("عفواً، لم أفهم الأمرْ")

    def on_voice_change(e):
        if app_state.get("voice_timer"):
            app_state["voice_timer"].cancel()
        app_state["voice_timer"] = threading.Timer(2.0, process_voice_command)
        app_state["voice_timer"].start()

    def close_voice_dialog(e):
        if app_state.get("voice_timer"):
            app_state["voice_timer"].cancel()
        voice_dialog.open = False
        page.update()

    voice_input_field = ft.TextField(
        label="أنا أسمعك.. قل أمرك",
        hint_text="اضغط مايك الكيبورد للتحدث...",
        autofocus=True,
        on_submit=process_voice_command,
        on_change=on_voice_change,
        width=300
    )

    voice_dialog = ft.AlertDialog(
        title=ft.Text("🎙️ التحدث مع ريكو"),
        content=voice_input_field,
        actions=[ft.TextButton("إلغاء", on_click=close_voice_dialog)]
    )
    page.overlay.append(voice_dialog)

    def manual_mic_click(e): 
        voice_input_field.value = "" 
        voice_dialog.open = True
        page.update()
        voice_input_field.focus() 
    # ----------------------------------------

    def on_voice_change(e):
        # كل ما الكيبورد يكتب حرف، نلغي العداد القديم
        if app_state.get("voice_timer"):
            app_state["voice_timer"].cancel()
        
        # نعمل عداد جديد.. لو سكت لمدة 2 ثانية، ينفذ الأمر لوحده!
        app_state["voice_timer"] = threading.Timer(2.0, process_voice_command)
        app_state["voice_timer"].start()

    def close_voice_dialog(e):
        if app_state.get("voice_timer"):
            app_state["voice_timer"].cancel()
        voice_dialog.open = False
        page.update()

    voice_input_field = ft.TextField(
        label="أنا أسمعك.. قل أمرك",
        hint_text="اضغط مايك الكيبورد للتحدث...",
        autofocus=True,
        on_submit=process_voice_command,
        on_change=on_voice_change,
        width=300
    )

    voice_dialog = ft.AlertDialog(
        title=ft.Text("🎙️ التحدث مع ريكو"),
        content=voice_input_field,
        actions=[ft.TextButton("إلغاء", on_click=close_voice_dialog)]
    )
    page.overlay.append(voice_dialog)

    def manual_mic_click(e): 
        voice_input_field.value = "" # تفريغ الخانة القديمة
        voice_dialog.open = True
        page.update()
        voice_input_field.focus() # توجيه الماوس للخانة فوراً عشان الكيبورد يفتح
    # ----------------------------------------

    # --- Register Tab UI ---
    dd_entity = ft.Dropdown(label="الكيان (المصدر)", width=155, height=45, bgcolor="white", text_size=12)
    txt_entity = ft.TextField(label="المصدر", width=155, height=45, bgcolor="white", border_radius=8, visible=False)
    btn_entity = ft.Container(content=ft.Text("+", color="white", size=20), bgcolor="#1976D2", width=40, height=40, border_radius=8, alignment=ft.Alignment(0,0))

    dd_type = ft.Dropdown(label="العملية", width=145, height=45, bgcolor="white", border_radius=8, text_size=12)
    dd_type.options = [ft.dropdown.Option(x) for x in ["مصروف", "إيراد", "تحويل داخلي", "تحويل عهدة", "تحويل خارجي"]]
    dd_type.value = "مصروف"
    txt_type = ft.TextField(label="العملية", width=145, height=45, bgcolor="white", border_radius=8, visible=False)
    btn_type = ft.Container(content=ft.Text("+", color="white", size=20), bgcolor="#1976D2", width=40, height=40, border_radius=8, alignment=ft.Alignment(0,0), visible=False)
    row_entity = ft.Row([dd_entity, txt_entity, btn_entity, dd_type, txt_type, btn_type], spacing=5, alignment="center")

    def populate_entity_dropdown():
        keys = sorted(list(PAYMENT_OPTS.keys()))
        dd_entity.options = [ft.dropdown.Option(k) for k in keys]
        try: dd_entity.update()
        except: pass

    def toggle_control_logic(dd, txt, btn, e=None, is_type=False):
        enable_cancel_btn()
        if btn.bgcolor == "red":
            txt.value = ""; txt.visible = False; txt.read_only = False; txt.bgcolor = "white"
            dd.visible = True; dd.value = None; btn.bgcolor = "#1976D2"; btn.content.value = "+"
            if is_type: btn.visible = False 
            if dd == dd_main:
                txt_sub.visible = False; dd_sub.visible = True; dd_sub.value = None; dd_sub.options = []
                btn_sub.content.value = "+"; btn_sub.bgcolor = "#1976D2"
                txt_sub.read_only = False; txt_sub.bgcolor = "white"
                try: dd_sub.update(); btn_sub.update(); txt_sub.update()
                except: pass
            if dd == dd_entity:
                populate_entity_dropdown(); dd_payment.value = None; dd_payment.options = []
                dd_main.value = None; dd_main.options = []; dd_sub.value = None; dd_sub.options = []
        else:
            is_manual = not txt.visible; dd.visible = not is_manual; txt.visible = is_manual
            btn.content.value = "x" if is_manual else "+"
        page.update()
        if dd == dd_entity or dd == dd_main:
            curr_ent = get_current_value(dd_entity, txt_entity)
            curr_main = get_current_value(dd_main, txt_main)
            update_dropdowns_logic(curr_ent, curr_main)

    btn_entity.on_click = lambda e: toggle_control_logic(dd_entity, txt_entity, btn_entity, e)
    btn_type.on_click = lambda e: toggle_control_logic(dd_type, txt_type, btn_type, e, is_type=True)

    txt_amount = ft.TextField(label="المبلغ", width=90, height=45, text_align="center", bgcolor="white", border_radius=8, on_submit=calc_general_submit)
    dd_payment = ft.Dropdown(label="طريقة الدفع", width=155, height=45, bgcolor="white", border_radius=8, text_size=12)
    txt_payment = ft.TextField(label="دفع جديد...", width=155, height=45, bgcolor="white", border_radius=8, visible=False)
    btn_payment = ft.Container(content=ft.Text("+", color="white", size=20), bgcolor="#1976D2", width=40, height=40, border_radius=8, alignment=ft.Alignment(0,0))
    row_payment = ft.Row([txt_amount, dd_payment, txt_payment, btn_payment], spacing=5, alignment="center")
    btn_payment.on_click = lambda e: toggle_control_logic(dd_payment, txt_payment, btn_payment, e)

    cb_gas_split = ft.Checkbox(label="توزيع تكلفة البنزين (⅓ بيت - ⅔ مكتبة)", visible=False, value=False)
    dd_main = ft.Dropdown(label="التصنيف الرئيسي", width=240, height=45, bgcolor="white", border_radius=8, text_size=12)
    txt_main = ft.TextField(label="جديد...", width=240, height=45, bgcolor="white", border_radius=8, visible=False)
    btn_main = ft.Container(content=ft.Text("+", color="white", size=20), bgcolor="#1976D2", width=40, height=40, border_radius=8, alignment=ft.Alignment(0,0))
    dd_sub = ft.Dropdown(label="التصنيف الفرعي", width=240, height=45, bgcolor="white", border_radius=8, text_size=12)
    txt_sub = ft.TextField(label="جديد...", width=240, height=45, bgcolor="white", border_radius=8, visible=False)
    btn_sub = ft.Container(content=ft.Text("+", color="white", size=20), bgcolor="#1976D2", width=40, height=40, border_radius=8, alignment=ft.Alignment(0,0))
    dd_main.toggle_btn = btn_main; dd_main.manual_txt = txt_main; dd_sub.toggle_btn = btn_sub; dd_sub.manual_txt = txt_sub
    row_main = ft.Row([dd_main, txt_main, btn_main], spacing=5, alignment="center")
    row_sub = ft.Row([dd_sub, txt_sub, btn_sub], spacing=5, alignment="center")
    btn_main.on_click = lambda e: toggle_control_logic(dd_main, txt_main, btn_main, e)
    btn_sub.on_click = lambda e: toggle_control_logic(dd_sub, txt_sub, btn_sub, e)
    txt_details = ft.TextField(label="تفاصيل...", multiline=True, width=300, height=60, bgcolor="white", border_radius=8)
    log_container = ft.Container(content=log_view, width=350, height=75, bgcolor="#f9f9f9", border=ft.border.all(1, "#dddddd"), border_radius=5, padding=5)

    def on_manual_change(e):
        app_state["confirm_save_flag"] = False; 
        if not app_state["row_to_edit"]:
            app_state["header_text"] = "✏️ تعديل..."; app_state["header_color"] = "blue"
            header_txt.value = app_state["header_text"]; header_txt.color = app_state["header_color"]; header_txt.update()
        enable_cancel_btn()

    def update_dropdowns_logic(entity_val, main_val=None):
        if not entity_val: entity_val = get_current_value(dd_entity, txt_entity)
        if entity_val: entity_val = entity_val.strip()
        if main_val: main_val = main_val.strip()

        if entity_val and config_data:
            relevant = [row for row in config_data if row[0].strip() == entity_val]
            cats_main = sorted(list(set([row[1].strip() for row in relevant if len(row) > 1 and row[1]])))
            if "ديون" not in cats_main: cats_main.append("ديون")
            dd_main.options = [ft.dropdown.Option(c) for c in cats_main]
        else: dd_main.options = []

        if entity_val and entity_val in PAYMENT_OPTS:
            dd_payment.options = [ft.dropdown.Option(p) for p in PAYMENT_OPTS[entity_val]]
            if dd_payment.value and dd_payment.value not in PAYMENT_OPTS[entity_val]: dd_payment.value = None
        
        if not main_val: main_val = get_current_value(dd_main, txt_main)

        if entity_val and main_val and config_data:
            if main_val == "ديون":
                debt_people = []
                for row in raw_data:
                    if len(row) > 4 and row[3].strip() == "ديون": 
                        name = row[4].strip(); 
                        if name: debt_people.append(name)
                relevant_subs = [r for r in config_data if r[0].strip() == entity_val and r[1].strip() == "ديون"]
                for r in relevant_subs: 
                     if len(r) > 2 and r[2]: debt_people.append(r[2].strip())
                unique_debt = sorted(list(set(debt_people)))
                dd_sub.options = [ft.dropdown.Option(p) for p in unique_debt]
            else:
                relevant_subs = [r for r in config_data if r[0].strip() == entity_val and r[1].strip() == main_val]
                sub_cats = sorted(list(set([r[2].strip() for r in relevant_subs if len(r) > 2 and r[2]])))
                dd_sub.options = [ft.dropdown.Option(c) for c in sub_cats]
        else: dd_sub.options = []
        try: dd_payment.update(); dd_main.update(); dd_sub.update()
        except: pass

    def on_entity_change_handler(e):
        val = dd_entity.value; on_manual_change(e)
        dd_payment.value = None; dd_main.value = None; dd_sub.value = None
        update_dropdowns_logic(val, None)

    def on_main_change_handler(e):
        # منع التصفير التلقائي أثناء تنفيذ الأوامر الصوتية
        if app_state["voice_mode"]: return
        
        val = dd_main.value; entity = dd_entity.value; on_manual_change(e)
        dd_sub.value = None; update_dropdowns_logic(entity, val)

    dd_entity.on_change = on_entity_change_handler
    dd_type.on_change = on_manual_change
    dd_payment.on_change = on_manual_change
    dd_main.on_change = on_main_change_handler
    dd_sub.on_change = on_manual_change
    txt_amount.on_change = lambda e: enable_cancel_btn()
    cb_gas_split.on_change = lambda e: enable_cancel_btn()
    txt_main.on_change = on_manual_change
    txt_sub.on_change = on_manual_change
    txt_payment.on_change = on_manual_change
    txt_entity.on_change = on_manual_change

    def reset_ui(keep_entity=True):
        txt_amount.value = ""; txt_details.value = ""
        cb_gas_split.value = False; cb_gas_split.visible = False
        for dd, txt, btn, is_type in [(dd_entity, txt_entity, btn_entity, False), (dd_type, txt_type, btn_type, True), (dd_payment, txt_payment, btn_payment, False), (dd_main, txt_main, btn_main, False), (dd_sub, txt_sub, btn_sub, False)]:
            dd.visible = True; dd.value = None; txt.visible = False; txt.read_only = False; txt.bgcolor = "white"; txt.value = ""; btn.content.value = "+"; btn.bgcolor = "#1976D2"
            if is_type: btn.visible = False 
        dd_type.value = "مصروف"; populate_entity_dropdown() 
        cancel_btn.disabled = True; cancel_btn.bgcolor = "grey"
        save_btn.disabled = True
        app_state["row_to_edit"] = None; app_state["confirm_save_flag"] = False
        try: page.update()
        except: pass

    def cancel_operation(e=None):
        reset_ui(); app_state["header_text"] = "🗑️ تم الإلغاء.. جاهز"; app_state["header_color"] = "grey"
        speak("تم إلغاءُ العمليهْ"); add_log("🚫 تم إلغاء العملية", "red"); trigger_listening_mode()
    cancel_btn.on_click = cancel_operation 

    def save_data(e=None):
        if not txt_amount.value: 
            txt_amount.focus(); page.update(); add_log("⚠️ خانة المبلغ فارغة", "red")
            speak("عفواً، كَمِ الْمَبْلَغْ؟") # نطق التحذير
            return False
        
        f_type = get_current_value(dd_type, txt_type)
        f_sub = get_current_value(dd_sub, txt_sub)
        
        if not txt_details.value:
            txt_details.value = f"{f_type} {txt_amount.value} {f_sub if f_sub else ''}"
            txt_details.update()

        f_entity = get_current_value(dd_entity, txt_entity)
        f_main = get_current_value(dd_main, txt_main)
        f_payment = get_current_value(dd_payment, txt_payment)

        if f_type in ["تحويل داخلي", "تحويل عهدة"]:
            if not f_entity or not f_sub: 
                add_log("⚠️ يجب تحديد المحول منه والمحول إليه", "red"); speak("حَدِّدِ الْمُحَوَّلَ مِنْهُ وَإِلَيْهْ"); return False
            if f_entity == f_sub and f_type == "تحويل داخلي": 
                add_log("⚠️ لا يمكن التحويل لنفس الكيان", "red"); speak("لا يُمْكِنُ التَّحْوِيلُ لِنَفْسِ الْكَيَانْ"); return False
            if f_payment == f_sub and f_type == "تحويل عهدة": 
                add_log("⚠️ لا يمكن التحويل لنفس الخزنة", "red"); speak("لا يُمْكِنُ التَّحْوِيلُ لِنَفْسِ الْخَزْنَة"); return False
        elif not cb_gas_split.value and not f_entity:
            if not f_entity: 
                add_log("⚠️ من فضلك اختر الكيان", "red"); speak("مِنْ فَضْلِكْ، حَدِّدِ الْكَيَانْ"); return False
        
        if not f_main: 
            add_log("⚠️ التصنيف الرئيسي مطلوب", "red"); speak("حَدِّدِ التَّصْنِيفَ الرَّئِيسِيْ"); return False
        if not f_sub: 
            add_log("⚠️ التصنيف الفرعي مطلوب", "red"); speak("حَدِّدِ التَّصْنِيفَ الْفَرْعِيْ"); return False
        if not f_payment: 
            add_log("⚠️ طريقة الدفع مطلوبة", "red"); speak("مِنْ فَضْلِكْ، حَدِّدْ طَرِيقَةَ الدَّفْعْ"); return False

        app_state["header_text"] = "💾 جاري الحفظ..."; page.update(); add_log("💾 بدأ عملية الحفظ...", "blue")
        try:
            current_time = datetime.now().strftime("%H:%M")
            date_str = f"{txt_custom_year.value}-{str(txt_custom_month.value).zfill(2)}-{str(txt_custom_day.value).zfill(2)} {current_time}"
            timestamp = date_str
            user = app_state["user_name"]
            
            rows_to_save = []
            if f_type == "تحويل داخلي":
                target_safe = f"نقدي {f_sub}"
                rows_to_save.append([timestamp, txt_amount.value, f"تحويل إلى {f_sub}", "تحويلات داخلية", f"إلى {f_sub}", f_entity, f_payment, user, "تحويل صادر"])
                rows_to_save.append([timestamp, txt_amount.value, f"تحويل من {f_entity}", "تحويلات داخلية", f"من {f_entity}", f_sub, target_safe, user, "تحويل وارد"])
            elif f_type == "تحويل عهدة":
                rows_to_save.append([timestamp, txt_amount.value, f"نقل إلى {f_sub}", "تحويلات عهدة", f"إلى {f_sub}", f_entity, f_payment, user, "تحويل صادر"])
                rows_to_save.append([timestamp, txt_amount.value, f"نقل من {f_payment}", "تحويلات عهدة", f"من {f_payment}", f_entity, f_sub, user, "تحويل وارد"])
            elif cb_gas_split.value and cb_gas_split.visible:
                total = float(txt_amount.value); h_share = int(total / 3); l_share = int(total - h_share)
                pay_method = f_payment if f_payment else f"عهدة {user}"
                rows_to_save.append([timestamp, str(h_share), f"{txt_details.value} (نصيب البيت)", f_main, f_sub, "البيت", pay_method, user, f_type])
                rows_to_save.append([timestamp, str(l_share), f"{txt_details.value} (نصيب المكتبة)", f_main, f_sub, "لافندر", pay_method, user, f_type])
            else:
                rows_to_save.append([timestamp, txt_amount.value, txt_details.value, f_main, f_sub, f_entity, f_payment, user, f_type])

            # --- هنا سحر الأوفلاين! ---
            if app_state.get("is_offline", False):
                for r in rows_to_save:
                    save_offline_transaction(r)
                    raw_data.append(r)
                app_state["header_text"] = "✅ تم الحفظ أوفلاين"; app_state["header_color"] = "orange"
                add_log("✅ تم حفظ العملية محلياً (أوفلاين)", "orange")
                reset_ui(keep_entity=True); check_sync_status(); update_offline_counter_ui()
                if txt_entity.visible: dd_entity.value = f_entity; page.update()
                return True

            # --- الحفظ الأونلاين (الكود الأصلي) ---
            if app_state["row_to_edit"]:
                delete_transaction_logic(app_state["row_to_edit"])
                app_state["row_to_edit"] = None 

            json_path = resource_path("credentials.json")
            scope = ["https://spreadsheets.google.com/feeds", "https://www.googleapis.com/auth/drive"]
            creds = ServiceAccountCredentials.from_json_keyfile_name(json_path, scope)
            client = gspread.authorize(creds)
            
            sheet_url = "Masrofat"
            conf_path = resource_path("app_config.json")
            if os.path.exists(conf_path):
                with open(conf_path, 'r') as f:
                    sheet_url = decode_base64(json.load(f).get("sheet_url", encode_base64("Masrofat")))
            
            sheet = client.open_by_url(sheet_url) if "http" in sheet_url else client.open(sheet_url)
            s_main = sheet.sheet1
            
            s_main.append_rows(rows_to_save)
            for r in rows_to_save: raw_data.append(r)

            if (txt_main.visible and not txt_main.read_only) or (txt_sub.visible and not txt_sub.read_only):
                if f_type not in ["تحويل داخلي", "تحويل عهدة"]:
                    new_entry = [f_entity, f_main, f_sub, "", ""]; exists = False
                    for r in config_data:
                        if len(r) >= 3 and r[0] == new_entry[0] and r[1] == new_entry[1] and r[2] == new_entry[2]: exists = True; break
                    if not exists: sheet.worksheet("Data").append_row(new_entry); config_data.append(new_entry)

            if txt_entity.visible and not txt_entity.read_only and f_entity and f_entity not in PAYMENT_OPTS:
                PAYMENT_OPTS[f_entity] = []; default_safe = f"نقدي {f_entity}"; PAYMENT_OPTS[f_entity].append(default_safe)
                new_config_row = [f_entity, "", "", "", default_safe]; sheet.worksheet("Data").append_row(new_config_row); config_data.append(new_config_row)

            if txt_payment.visible and not txt_payment.read_only and f_payment and f_entity in PAYMENT_OPTS and f_payment not in PAYMENT_OPTS[f_entity]:
                PAYMENT_OPTS[f_entity].append(f_payment); payment_row = [f_entity, "", "", "", f_payment]
                sheet.worksheet("Data").append_row(payment_row); config_data.append(payment_row)

            app_state["header_text"] = "✅ تمام.. حفظت العملية"; app_state["header_color"] = "green"
            add_log("✅ تم حفظ البيانات بنجاح", "green"); speak("تم حفظُ العمليةِ بنجاحْ"); 
            reset_ui(keep_entity=True); trigger_refresh_thread() 
            if txt_entity.visible: dd_entity.value = f_entity; page.update()
            return True

        except Exception as e:
            app_state["header_text"] = "❌ خطأ في الحفظ"; app_state["header_color"] = "red"; page.update(); add_log(f"❌ خطأ: {e}", "red"); speak("حدث خطأ أثناء الحفظ"); return False

    # --- Balances Tab (Updated Logic) ---
    balances_container = ft.Column(scroll=ft.ScrollMode.AUTO, spacing=10, horizontal_alignment=ft.CrossAxisAlignment.CENTER)
    transactions_container = ft.Column(scroll=ft.ScrollMode.AUTO, spacing=10, horizontal_alignment="center")

    def delete_transaction_logic(row_data):

        app_state["header_text"] = "🗑️ جاري الحذف..."; app_state["header_color"] = "red"; page.update()
        try:
            # --- تعديل: استخدام المسار الصحيح للملف ---
            current_dir = os.path.dirname(os.path.abspath(__file__))
            json_path = os.path.join(current_dir, "credentials.json")

            scope = ["https://spreadsheets.google.com/feeds", "https://www.googleapis.com/auth/drive"]
            creds = ServiceAccountCredentials.from_json_keyfile_name(json_path, scope)
            client = gspread.authorize(creds); sheet_main = client.open("Masrofat").sheet1
            target_ts = row_data[0]; target_amt = row_data[1]; rows_to_delete = []
            all_values = sheet_main.get_all_values()
            for idx, row in enumerate(all_values):
                if idx == 0: continue 
                if row[0] == target_ts and row[1] == target_amt: rows_to_delete.append(idx + 1) 
            for r_idx in sorted(rows_to_delete, reverse=True): sheet_main.delete_rows(r_idx)
            global raw_data; raw_data = [r for r in raw_data if not (r[0] == target_ts and r[1] == target_amt)]
            app_state["header_text"] = "✅ تم الحذف"; app_state["header_color"] = "green"; page.update()
            add_log("🗑️ تم حذف العملية", "red"); trigger_refresh_thread()
        except Exception as e:
            app_state["header_text"] = "❌ خطأ في الحذف"; app_state["header_color"] = "red"; page.update(); add_log(f"❌ فشل الحذف: {e}", "red")

    def edit_transaction(row_data):
        try:
            txt_amount.value = row_data[1].strip(); txt_details.value = row_data[2].strip()
            def set_read_only_mode(dd, txt, btn, value, is_type=False):
                dd.visible = False; txt.visible = True; txt.value = value; txt.read_only = True; txt.bgcolor = "#FFF9C4"; btn.content.value = "X"; btn.bgcolor = "red"
                if is_type: btn.visible = True
            entity_val = row_data[5].strip(); set_read_only_mode(dd_entity, txt_entity, btn_entity, entity_val)
            type_val = row_data[8].strip(); set_read_only_mode(dd_type, txt_type, btn_type, type_val, is_type=True)
            pay_val = row_data[6].strip(); set_read_only_mode(dd_payment, txt_payment, btn_payment, pay_val)
            main_val = row_data[3].strip(); set_read_only_mode(dd_main, txt_main, btn_main, main_val)
            sub_val = row_data[4].strip(); set_read_only_mode(dd_sub, txt_sub, btn_sub, sub_val)
            enable_cancel_btn(); app_state["row_to_edit"] = row_data
            nav_click(type("", (), {"control": type("", (), {"data": "reg"})()})())
            app_state["header_text"] = "✏️ وضع التعديل (محمي)"; app_state["header_color"] = "blue"; page.update(); add_log("✏️ تم استدعاء البيانات للتعديل", "blue")
        except Exception as e: add_log(f"❌ خطأ في الاستدعاء: {e}", "red")

    def update_balances_view_ui():
        if not raw_data: return
        ent_total = {}; ent_details = {}
        safe_total = {}; safe_details = {}
        debt_people_bal = {} 

        for row in raw_data:
            if len(row) < 9: continue
            try:
                amt = float(row[1]) if row[1] else 0
                r_ent = row[5]; r_safe = row[6]; r_type = row[8]
                r_main = row[3].strip(); r_sub = row[4].strip()

                if r_ent and r_safe:
                    if r_ent not in ent_total: ent_total[r_ent] = 0; ent_details[r_ent] = {}
                    if r_safe not in safe_total: safe_total[r_safe] = 0; safe_details[r_safe] = {}
                    if r_safe not in ent_details[r_ent]: ent_details[r_ent][r_safe] = 0
                    if r_ent not in safe_details[r_safe]: safe_details[r_safe][r_ent] = 0
                    if r_type in ["إيراد", "تحويل وارد"]:
                        ent_total[r_ent] += amt; ent_details[r_ent][r_safe] += amt
                        safe_total[r_safe] += amt; safe_details[r_safe][r_ent] += amt
                    elif r_type in ["مصروف", "تحويل صادر", "تحويل خارجي"]:
                        ent_total[r_ent] -= amt; ent_details[r_ent][r_safe] -= amt
                        safe_total[r_safe] -= amt; safe_details[r_safe][r_ent] -= amt
                
                if r_main == "ديون":
                    if r_sub not in debt_people_bal: debt_people_bal[r_sub] = 0
                    if r_type == "مصروف": debt_people_bal[r_sub] += amt 
                    elif r_type == "إيراد": debt_people_bal[r_sub] -= amt 

            except: pass
        
        total_to_me = 0; details_to_me = {}
        total_on_me = 0; details_on_me = {}
        for person, bal in debt_people_bal.items():
            if bal > 0: total_to_me += bal; details_to_me[person] = bal
            elif bal < 0: total_on_me += abs(bal); details_on_me[person] = abs(bal)
        net_debt = total_to_me - total_on_me

        total_entities_bal = sum(ent_total.values())
        net_assets = total_entities_bal + net_debt

        balances_container.controls.clear()
        balances_container.controls.append(ft.ElevatedButton("تحديث من السيرفر 🔄", on_click=lambda e: trigger_refresh_thread(), bgcolor="#1565C0", color="white"))
        
        balances_container.controls.append(
            ft.Container(
                content=ft.Column([
                    ft.Text("صافي الأصول (ثروتك الحقيقية)", size=12, color="white", weight="bold"),
                    ft.Text(f"{net_assets:,.0f}", size=20, color="white", weight="bold")
                ], alignment=ft.MainAxisAlignment.CENTER, horizontal_alignment=ft.CrossAxisAlignment.CENTER),
                bgcolor="#455A64", width=200, height=60, border_radius=10, padding=5, margin=5
            )
        )
        
        balances_container.controls.append(ft.Container(height=2, bgcolor="#eeeeee", border_radius=5, width=300))
        balances_container.controls.append(ft.Text("🤝 الديون (ليك وعليك)", weight="bold", size=16, text_align="center"))
        
        row_debts = ft.Row(scroll=ft.ScrollMode.HIDDEN, spacing=10, alignment=ft.MainAxisAlignment.CENTER)
        row_debts.controls.append(ft.Container(content=ft.Column([ft.Text("صافي الديون", size=12, color="white", weight="bold"), ft.Text(f"{net_debt:,.0f}", size=14, color="white", weight="bold"), ft.Icon( ft.icons.CALCULATE, color="white70", size=16)], alignment=ft.MainAxisAlignment.CENTER, spacing=2), bgcolor="blue", width=100, height=80, border_radius=10, padding=5))
        if total_to_me > 0:
             row_debts.controls.append(ft.Container(content=ft.Column([ft.Text("لي (دائن)", size=12, color="white", weight="bold"), ft.Text(f"{total_to_me:,.0f}", size=14, color="white", weight="bold"), ft.Icon( ft.icons.ARROW_UPWARD, color="white70", size=16)], alignment=ft.MainAxisAlignment.CENTER, spacing=2), bgcolor="green", width=100, height=80, border_radius=10, padding=5, on_click=on_box_click, data={"name": "الديون لي", "total": total_to_me, "breakdown": details_to_me}))
        if total_on_me > 0:
             row_debts.controls.append(ft.Container(content=ft.Column([ft.Text("علي (مدين)", size=12, color="white", weight="bold"), ft.Text(f"{total_on_me:,.0f}", size=14, color="white", weight="bold"), ft.Icon( ft.icons.ARROW_DOWNWARD, color="white70", size=16)], alignment=ft.MainAxisAlignment.CENTER, spacing=2), bgcolor="red", width=100, height=80, border_radius=10, padding=5, on_click=on_box_click, data={"name": "الديون علي", "total": total_on_me, "breakdown": details_on_me}))
        balances_container.controls.append(row_debts)

        balances_container.controls.append(ft.Container(height=2, bgcolor="#eeeeee", border_radius=5, width=300))
        balances_container.controls.append(ft.Text("🏢 الكيانات (أين أموالك؟)", weight="bold", size=16, text_align="center"))
        
        row_entities = ft.Row(scroll=ft.ScrollMode.HIDDEN, spacing=10, alignment=ft.MainAxisAlignment.CENTER)
        row_entities.controls.append(ft.Container(content=ft.Column([ft.Text("إجمالي الكيانات", size=11, color="white", weight="bold"), ft.Text(f"{total_entities_bal:,.0f}", size=14, color="white", weight="bold"), ft.Icon( ft.icons.STORE, color="white70", size=16)], alignment=ft.MainAxisAlignment.CENTER, spacing=2), bgcolor="#E65100", width=100, height=80, border_radius=10, padding=5))
        
        for ent, val in ent_total.items():
            if val == 0: continue
            row_entities.controls.append(ft.Container(content=ft.Column([ft.Text(ent, size=12, color="white", weight="bold"), ft.Text(f"{val:,.0f}", size=14, color="white", weight="bold"), ft.Icon( ft.icons.INFO_OUTLINE, color="white70", size=16)], alignment=ft.MainAxisAlignment.CENTER, spacing=2), bgcolor="#1976D2", width=100, height=80, border_radius=10, padding=5, on_click=on_box_click, data={"name": ent, "total": val, "breakdown": ent_details[ent]}))
        balances_container.controls.append(row_entities)
        
        balances_container.controls.append(ft.Container(height=2, bgcolor="#eeeeee", border_radius=5, width=300))
        balances_container.controls.append(ft.Text("💰 الخزن والعهد (لمن هذه الأموال؟)", weight="bold", size=16, text_align="center"))
        
        row_safes = ft.Row(scroll=ft.ScrollMode.HIDDEN, spacing=10, alignment=ft.MainAxisAlignment.CENTER)
        for safe, val in safe_total.items():
            if val == 0: continue
            row_safes.controls.append(ft.Container(content=ft.Column([ft.Text(safe, size=12, color="white", weight="bold"), ft.Text(f"{val:,.0f}", size=14, color="white", weight="bold"), ft.Icon( ft.icons.INFO_OUTLINE, color="white70", size=16)], alignment=ft.MainAxisAlignment.CENTER, spacing=2), bgcolor="#388E3C", width=100, height=80, border_radius=10, padding=5, on_click=on_box_click, data={"name": safe, "total": val, "breakdown": safe_details[safe]}))
        balances_container.controls.append(row_safes)
        
        transactions_container.controls.clear()
        transactions_container.controls.append(ft.ElevatedButton("تحديث من السيرفر 🔄", on_click=lambda e: trigger_refresh_thread(), bgcolor="#1565C0", color="white"))
        dt_rows = []
        for t in reversed(raw_data[-30:]): 
            if len(t) < 9: continue
            edit_btn = ft.TextButton("✏️", data=t, on_click=lambda e: edit_transaction(e.control.data), style=ft.ButtonStyle(color="blue"))
            del_btn = ft.TextButton("❌", data=t, on_click=lambda e: app_state.update({"row_to_delete": e.control.data}) or dlg_modal.open or page.update() or setattr(dlg_modal, "open", True) or page.update(), style=ft.ButtonStyle(color="red"))
            dt_rows.append(ft.DataRow(cells=[ft.DataCell(ft.Text(t[0][:10], size=10)), ft.DataCell(ft.Text(t[1], weight="bold", size=11)), ft.DataCell(ft.Text(t[8], size=10)), ft.DataCell(ft.Text(t[5], size=10)), ft.DataCell(ft.Text(t[2], size=10, overflow=ft.TextOverflow.ELLIPSIS)), ft.DataCell(edit_btn), ft.DataCell(del_btn)]))
        data_table = ft.DataTable(columns=[ft.DataColumn(ft.Text("التاريخ")), ft.DataColumn(ft.Text("المبلغ")), ft.DataColumn(ft.Text("النوع")), ft.DataColumn(ft.Text("الكيان")), ft.DataColumn(ft.Text("تفاصيل")), ft.DataColumn(ft.Text("تعديل")), ft.DataColumn(ft.Text("حذف"))], rows=dt_rows, column_spacing=5)
        transactions_container.controls.append(ft.Container(content=data_table, border=ft.border.all(1, "#eeeeee"), border_radius=5))
        
        page.update(); 

    def trigger_refresh_thread():
        add_log("🔄 جاري تحديث البيانات من السيرفر...", "blue")
        threading.Thread(target=refresh_data_logic, daemon=True).start()

    def refresh_data_logic():
        load_data_background() 
        update_balances_view_ui() 

    # --- تعريف شاشات التطبيق الأساسية ---
    screen_register = ft.Container(visible=True, padding=5, expand=True, content=ft.Column([

        ft.Row([header_txt, timer_lbl], alignment="center", spacing=10),
        offline_count_txt,
        btn_sync,
        row_custom_date, # Date UI

        ft.Row([ft.ElevatedButton(content=ft.Row([ft.Text("🎙️"), ft.Text("اضغط للتحدث")], alignment="center"), on_click=manual_mic_click, bgcolor="#1565C0", color="white", width=220, height=45), cancel_btn], alignment="center", spacing=5),
        row_entity, row_payment, row_main, row_sub, cb_gas_split, txt_details,
        ft.Container(content=save_btn, margin=ft.margin.only(top=-10))
    ], horizontal_alignment="center", spacing=10, scroll=ft.ScrollMode.AUTO))
    
    screen_balances = ft.Container(visible=False, padding=10, expand=True, content=balances_container)
    screen_transactions = ft.Container(visible=False, padding=10, expand=True, content=transactions_container)

    # --- Reports Tab ---
    screen_reports = ft.Container(visible=False, padding=10, expand=True)
    def open_rep_dialog(target_type):
        if not raw_data: return
        app_state["current_rep_target"] = target_type
        choice_list.controls.clear()
        items = []
        if target_type == "rep_entity":
            ents = sorted(list(set([r[5] for r in raw_data if len(r)>5])))
            items = ["الكل"] + ents
        elif target_type == "rep_period":
            items = ["الشهر الحالي", "الشهر السابق", "الكل", "مخصص"]
        elif target_type == "rep_main":
            cats = sorted(list(set([r[3] for r in raw_data if len(r)>3 and r[8]=="مصروف"])))
            items = ["الكل"] + cats
        elif target_type == "rep_sub":
            main_cat = rep_state["main"]
            if main_cat == "الكل": items = []
            else:
                relevant = [r[4] for r in raw_data if len(r)>4 and r[3]==main_cat and r[8]=="مصروف"]
                items = ["الكل"] + sorted(list(set(relevant)))
        for item in items:
            choice_list.controls.append(ft.ListTile(title=ft.Text(item), data=item, on_click=on_choice_click))
        dlg_choice.title.value = "اختر..."
        dlg_choice.open = True
        app_state["is_dialog_open"] = True
        page.update()

    btn_rep_entity = ft.ElevatedButton(content=ft.Text("الكيان: الكل", color="black", size=11), width=100, bgcolor="white", style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=5), padding=2), on_click=lambda e: open_rep_dialog("rep_entity"))
    btn_rep_period = ft.ElevatedButton(content=ft.Text("الفترة: الشهر الحالي", color="black", size=11), width=120, bgcolor="white", style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=5), padding=2), on_click=lambda e: open_rep_dialog("rep_period"))
    btn_rep_main = ft.ElevatedButton(content=ft.Text("رئيسي: الكل", color="black", size=11), width=100, bgcolor="white", style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=5), padding=2), on_click=lambda e: open_rep_dialog("rep_main"))
    btn_rep_sub = ft.ElevatedButton(content=ft.Text("فرعي: الكل", color="black", size=11), width=100, bgcolor="#eeeeee", disabled=True, style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=5), padding=2), on_click=lambda e: open_rep_dialog("rep_sub"))
    
    report_results = ft.Column(scroll=ft.ScrollMode.AUTO, expand=True, horizontal_alignment=ft.CrossAxisAlignment.CENTER)
    
    # --- Defined BEFORE Use in screen_reports.content ---
    def validate_report_date(e=None):
        try:
            for ctrl in [rep_txt_day, rep_txt_month, rep_txt_year]:
                if not ctrl.value.isdigit() and ctrl.value != "":
                    ctrl.value = "".join(filter(str.isdigit, ctrl.value))
                    ctrl.update()
        except: pass

    rep_txt_day = ft.TextField(hint_text="DD", width=40, text_align="center", max_length=2, border=ft.InputBorder.UNDERLINE, bgcolor="white", text_size=12, on_change=validate_report_date)
    rep_txt_month = ft.TextField(hint_text="MM", width=40, text_align="center", max_length=2, border=ft.InputBorder.UNDERLINE, bgcolor="white", text_size=12, on_change=validate_report_date)
    rep_txt_year = ft.TextField(hint_text="YYYY", width=60, text_align="center", max_length=4, border=ft.InputBorder.UNDERLINE, bgcolor="white", text_size=12, on_change=validate_report_date)
    rep_date_input_row = ft.Row([rep_txt_day, ft.Text("/", size=16, color="grey"), rep_txt_month, ft.Text("/", size=16, color="grey"), rep_txt_year], alignment=ft.MainAxisAlignment.CENTER, visible=False)
    
    # Now use it
    screen_reports.content = ft.Column([
        ft.Row([btn_rep_entity, btn_rep_period], alignment=ft.MainAxisAlignment.CENTER, spacing=5), 
        ft.Row([btn_rep_main, btn_rep_sub], alignment=ft.MainAxisAlignment.CENTER, spacing=5), 
        rep_date_input_row, 
        ft.Divider(height=1), 
        report_results
    ])

    def update_report_view(e=None):
        if not raw_data: return
        target_ent = rep_state["entity"]; target_per = rep_state["period"]; target_cat = rep_state["main"]; target_sub = rep_state["sub"]
        is_custom = target_per == "مخصص"
        # Update visibility
        rep_date_input_row.visible = is_custom 
        page.update()
        
        now = datetime.now(); filtered = []
        for r in raw_data:
            if len(r)<9: continue
            try:
                rd = datetime.strptime(r[0][:10], "%Y-%m-%d")
                if target_ent != "الكل" and r[5] != target_ent: continue
                if target_cat != "الكل" and r[3] != target_cat: continue
                if target_sub != "الكل" and r[4] != target_sub: continue
                if target_per == "الشهر الحالي" and (rd.month != now.month or rd.year != now.year): continue
                if target_per == "الشهر السابق":
                    lm = now.month - 1 if now.month > 1 else 12
                    ly = now.year if now.month > 1 else now.year - 1
                    if rd.month != lm or rd.year != ly: continue
                if target_per == "مخصص":
                    # Logic can be enhanced to use the new rep_txt fields if needed, 
                    # for now relying on datepicker or manual logic is placeholder.
                    pass
                filtered.append(r)
            except: pass
        t_out = 0; cats = {}
        for r in filtered:
            if r[8] == "مصروف":
                amt = float(r[1])
                t_out += amt
                key = r[4] if target_cat != "الكل" else r[3]
                cats[key] = cats.get(key, 0) + amt
        report_results.controls.clear()
        report_results.controls.append(ft.Text(f"💸 إجمالي المصروفات: {t_out:,.0f}", size=16, weight="bold", color="red"))
        report_results.controls.append(ft.Divider())
        for c, v in sorted(cats.items(), key=lambda x: x[1], reverse=True): 
            p = (v/t_out) if t_out else 0
            report_results.controls.append(ft.Container(content=ft.Column([ft.Row([ft.Text(c, size=12, weight="bold"), ft.Text(f"{v:,.0f} ({int(p*100)}%)", size=12)], alignment=ft.MainAxisAlignment.SPACE_BETWEEN), ft.ProgressBar(value=p, color="red", bgcolor="#eee", height=8)], spacing=2), padding=5, bgcolor="white", border_radius=5))
        page.update()

    # --- Cash Counting Tab ---
    screen_cash_counting = ft.Container(visible=False, padding=10, expand=True)
    cash_state = {"selected_safe_balance": 0.0, "current_safe_name": "الكل"}
    btn_select_safe = ft.ElevatedButton(text="الكل", color="black", icon=ft.icons.ARROW_DROP_DOWN, width=200, bgcolor="white", on_click=lambda e: open_safe_dialog())
    lbl_expected = ft.Text("الرصيد الدفتري: 0", size=14, weight="bold", color="grey")
    lbl_actual = ft.Text("الرصيد الفعلي (العد): 0", size=14, weight="bold", color="blue")
    lbl_status = ft.Text("---", size=16, weight="bold")
    denoms = [200, 100, 50, 20, 10, 5, 1, 0.5]
    cash_inputs = {} 
    cash_outputs = {} 
    input_controls_list = [] 

    def open_safe_dialog():
        if not raw_data: return
        app_state["current_rep_target"] = "cash"
        safes = set()
        for r in raw_data:
            if len(r) > 6 and r[6]: safes.add(str(r[6]).strip())
        for k, v in PAYMENT_OPTS.items():
            for s in v: safes.add(str(s).strip())
        sorted_safes = sorted(list(safes))
        choice_list.controls.clear()
        choice_list.controls.append(ft.ListTile(title=ft.Text("الكل"), data="الكل", on_click=on_choice_click))
        for s in sorted_safes:
            choice_list.controls.append(ft.ListTile(title=ft.Text(s), data=s, on_click=on_choice_click))
        dlg_choice.title.value = "اختر الخزنة"; dlg_choice.open = True; app_state["is_dialog_open"] = True; page.update()

    def on_safe_changed(safe_name):
        cash_state["current_safe_name"] = safe_name
        for d in denoms:
            cash_inputs[d].value = ""; cash_outputs[d].value = "0"
            try: cash_inputs[d].update(); cash_outputs[d].update()
            except: pass
        calc_cash_logic()

    def calc_cash_logic(e=None):
        safe_name = cash_state["current_safe_name"]
        bal = get_safe_balance(safe_name)
        cash_state["selected_safe_balance"] = bal
        lbl_expected.value = f"الرصيد الدفتري ({safe_name}): {bal:,.1f}"
        try: lbl_expected.update()
        except: pass
        total_cash = 0.0
        for d in denoms:
            try: val = float(cash_inputs[d].value) if cash_inputs[d].value else 0
            except: val = 0
            row_sum = val * d
            total_cash += row_sum
            cash_outputs[d].value = f"{row_sum:,.1f}".replace(".0", "") 
            try: cash_outputs[d].update()
            except: pass
        lbl_actual.value = f"الرصيد الفعلي: {total_cash:,.1f}"
        try: lbl_actual.update()
        except: pass
        diff = total_cash - cash_state["selected_safe_balance"]
        if abs(diff) < 0.1: lbl_status.value = "✅ مضبوط (تمام)"; lbl_status.color = "green"
        elif diff > 0: lbl_status.value = f"🔵 زيادة: {diff:,.1f}"; lbl_status.color = "blue"
        else: lbl_status.value = f"🔴 عجز: {abs(diff):,.1f}"; lbl_status.color = "red"
        try: lbl_status.update()
        except: pass
        if e and e.control:
            threading.Thread(target=delayed_auto_focus, args=(e.control,), daemon=True).start()

    def delayed_auto_focus(ctrl):
        current_val = ctrl.value
        time.sleep(5) 
        if ctrl.value == current_val and ctrl.value != "":
            try:
                idx = input_controls_list.index(ctrl)
                if idx + 1 < len(input_controls_list):
                    input_controls_list[idx+1].focus()
                    page.update()
            except: pass

    def focus_next(e):
        try:
            idx = input_controls_list.index(e.control)
            if idx + 1 < len(input_controls_list):
                input_controls_list[idx+1].focus()
        except: pass

    cash_rows_ui = []
    cash_rows_ui.append(ft.Row([ft.Text("الفئة", width=60, weight="bold", text_align="center", size=12), ft.Text("العدد", width=80, weight="bold", text_align="center", size=12), ft.Text("الإجمالي", width=80, weight="bold", text_align="center", size=12)], alignment=ft.MainAxisAlignment.CENTER))
    for d in denoms:
        txt_count = ft.TextField(
            width=80, height=30, text_size=12, text_align="center", 
            keyboard_type=ft.KeyboardType.NUMBER, content_padding=3, bgcolor="white", 
            on_submit=calc_cash_submit # تم ربط منطق الحساب هنا
        )
        txt_count.on_change = calc_cash_logic 
        cash_inputs[d] = txt_count
        input_controls_list.append(txt_count) 
        txt_row_sum = ft.Text("0", width=80, text_align="center", size=12)
        cash_outputs[d] = txt_row_sum
        row = ft.Row([ft.Text(str(d), width=60, text_align="center", weight="bold", size=12), txt_count, txt_row_sum], alignment=ft.MainAxisAlignment.CENTER)
        cash_rows_ui.append(row)
    screen_cash_counting.content = ft.Column([ft.Container(height=5), ft.Row([btn_select_safe], alignment=ft.MainAxisAlignment.CENTER), ft.Divider(height=1), ft.Column(cash_rows_ui, scroll=ft.ScrollMode.AUTO, height=260, spacing=0), ft.Column([lbl_expected, lbl_actual, lbl_status], horizontal_alignment=ft.CrossAxisAlignment.CENTER, spacing=0)], scroll=ft.ScrollMode.AUTO, horizontal_alignment=ft.CrossAxisAlignment.CENTER, spacing=2)

# --- Settings & Dictionary ---
    # 1. قسم بياناتي (متاح للجميع)
    txt_my_user = ft.TextField(label="اسم المستخدم (للتغيير)", width=250, height=45, text_size=12)
    txt_my_email = ft.TextField(label="البريد الإلكتروني (لاستعادة الباسورد)", width=250, height=45, text_size=12)
    txt_old_pass = ft.TextField(label="كلمة المرور القديمة", password=True, can_reveal_password=True, width=250, height=45, text_size=12)
    txt_new_pass = ft.TextField(label="كلمة المرور الجديدة", password=True, can_reveal_password=True, width=250, height=45, text_size=12)

    def change_my_data_logic(e):
        u = app_state["user_name"]
        new_u = txt_my_user.value.strip() or u
        new_email = txt_my_email.value.strip()
        old_p = txt_old_pass.value.strip(); new_p = txt_new_pass.value.strip()
        
        if not old_p or not new_p: add_log("⚠️ يرجى إدخال كلمة المرور القديمة والجديدة", "red"); page.update(); return

        try:
            db_path = resource_path("users_db.json")
            with open(db_path, "r", encoding="utf-8") as f: db = json.load(f)
            
            if decode_base64(db[u]["pass"]) != old_p:
                add_log("❌ كلمة المرور القديمة غير صحيحة", "red"); page.update(); return

            user_data = db.pop(u)
            user_data["pass"] = encode_base64(new_p)
            user_data["email"] = new_email
            db[new_u] = user_data
            with open(db_path, "w", encoding="utf-8") as f: json.dump(db, f, ensure_ascii=False)
            
            # مسح ملف التذكر للبدء بنظافة
            session_path = resource_path("session.json")
            if os.path.exists(session_path): os.remove(session_path)

            add_log("✅ تم الحفظ. يرجى تسجيل الدخول مجدداً", "green"); speak("تم تغييرُ البياناتِ بنجاحْ")
            
            app_state["user_name"] = ""; app_state["user_role"] = "user"
            txt_my_user.value = ""; txt_my_email.value = ""; txt_old_pass.value = ""; txt_new_pass.value = ""
            screen_settings.visible = False; screen_login.visible = True
            log_u.value = new_u; log_p.value = ""
            page.update()
        except Exception as ex: add_log(f"❌ خطأ: {ex}", "red")

    password_section = ft.Column([
        ft.Text("👤 بياناتي الشخصية", weight="bold", size=14, color="blue"),
        txt_my_user, txt_my_email, txt_old_pass, txt_new_pass,
        ft.ElevatedButton("💾 حفظ التعديلات والخروج", on_click=change_my_data_logic, bgcolor="blue", color="white")
    ], horizontal_alignment="center", spacing=5)

    # 2. قسم إدارة المستخدمين (يظهر للأدمن فقط)
    users_list_view = ft.ListView(expand=True, spacing=5, height=220)
    
    adm_txt_user = ft.TextField(label="اسم المستخدم", width=120, height=40, text_size=12)
    adm_txt_email = ft.TextField(label="الإيميل", width=120, height=40, text_size=12)
    adm_txt_pass = ft.TextField(label="كلمة المرور", password=True, can_reveal_password=True, width=120, height=40, text_size=12)
    adm_cb_admin = ft.Checkbox(label="أدمن", value=False)
    adm_cb_rep = ft.Checkbox(label="تقارير", value=False)
    adm_cb_bal = ft.Checkbox(label="أرصدة", value=False)

# استخدمنا content بدل text عشان مستحيل يعلق
    adm_btn_save = ft.ElevatedButton(content=ft.Text("إضافة جديد", color="white", weight="bold"), bgcolor="green", height=40)

    # الزرار الذكي (الحرباء)
    def adm_on_user_change(e):
        try:
            db_path = resource_path("users_db.json")
            with open(db_path, "r", encoding="utf-8") as f: db = json.load(f)
            if adm_txt_user.value.strip() in db:
                adm_btn_save.content.value = "حفظ التعديلات"
                adm_btn_save.bgcolor = "blue"
            else:
                adm_btn_save.content.value = "إضافة جديد"
                adm_btn_save.bgcolor = "green"
            adm_btn_save.update()
        except: pass
    adm_txt_user.on_change = adm_on_user_change

    def adm_on_admin_check(e):
        if adm_cb_admin.value:
            adm_cb_rep.value = True; adm_cb_bal.value = True
            adm_cb_rep.update(); adm_cb_bal.update()
    adm_cb_admin.on_change = adm_on_admin_check

    def load_users_table():
        users_list_view.controls.clear()
        try:
            db_path = resource_path("users_db.json")
            with open(db_path, "r", encoding="utf-8") as f: db = json.load(f)

            for uname, data in db.items():
                is_admin = data.get("role") == "admin"
                role_icon = "👑" if is_admin else "👤"
                
                def edit_user_logic(e, target=uname):
                    # رفع البيانات للخانات
                    adm_txt_user.value = target
                    adm_txt_email.value = db[target].get("email", "")
                    adm_txt_pass.value = "" 
                    adm_cb_admin.value = (db[target].get("role") == "admin")
                    adm_cb_rep.value = db[target].get("reports", False)
                    adm_cb_bal.value = db[target].get("balances", False)
                    
                    # تحويل الزرار فوراً لحالة التعديل
                    adm_btn_save.content.value = "حفظ التعديلات"
                    adm_btn_save.bgcolor = "blue"
                    adm_btn_save.update()
                    page.update()

                def delete_user_logic(e, target=uname):
                    if target == app_state["user_name"]:
                        add_log("⚠️ لا يمكنك حذف حسابك الحالي", "red"); return
                    with open(db_path, "r", encoding="utf-8") as f: temp_db = json.load(f)
                    if target in temp_db: del temp_db[target]
                    with open(db_path, "w", encoding="utf-8") as f: json.dump(temp_db, f, ensure_ascii=False)
                    load_users_table(); add_log(f"🗑️ تم حذف: {target}", "red")

                edit_btn = ft.IconButton( ft.icons.EDIT, icon_color="blue", on_click=edit_user_logic, tooltip="تعديل")
                del_btn = ft.IconButton( ft.icons.DELETE, icon_color="red", on_click=delete_user_logic, tooltip="حذف")
                if uname == app_state["user_name"]: del_btn.visible = False 

                row = ft.Container(
                    content=ft.Row([
                        ft.Text(f"{role_icon} {uname}", weight="bold", size=14, width=150),
                        ft.Row([edit_btn, del_btn], spacing=0)
                    ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN), padding=5, bgcolor="white", border_radius=8, border=ft.border.all(1, "#eeeeee")
                )
                users_list_view.controls.append(row)
        except Exception as ex: add_log(f"خطأ: {ex}", "red")
        if users_list_view.page: users_list_view.update()

    def add_edit_user_logic(e):
        u = adm_txt_user.value.strip(); p = adm_txt_pass.value.strip(); em = adm_txt_email.value.strip()
        if not u: return
        try:
            db_path = resource_path("users_db.json")
            with open(db_path, "r", encoding="utf-8") as f: db = json.load(f)
            
            if u not in db and not p:
                add_log("⚠️ يرجى إدخال كلمة مرور للمستخدم الجديد", "red"); return
                
            final_pass = encode_base64(p) if p else db[u]["pass"]
            
            if u in db: add_log(f"✅ تم تعديل بيانات: {u}", "blue")
            else: add_log(f"✅ تم إضافة المستخدم: {u}", "green")
            
            db[u] = {"pass": final_pass, "email": em, "role": "admin" if adm_cb_admin.value else "user", "reports": adm_cb_rep.value, "balances": adm_cb_bal.value}
            with open(db_path, "w", encoding="utf-8") as f: json.dump(db, f, ensure_ascii=False)
            
            # تفريغ الخانات
            adm_txt_user.value = ""; adm_txt_pass.value = ""; adm_txt_email.value = ""
            adm_cb_admin.value = False; adm_cb_rep.value = False; adm_cb_bal.value = False
            
            # إرجاع الزرار لحالة الإضافة الجديدة
            adm_btn_save.content.value = "إضافة جديد"
            adm_btn_save.bgcolor = "green"
            adm_btn_save.update()
            
            load_users_table()
        except Exception as ex: pass

    adm_btn_save.on_click = add_edit_user_logic

    admin_panel = ft.Column([
        ft.Divider(),
        ft.Text("👑 إدارة المستخدمين (للمديرين فقط)", weight="bold", size=14, color="green"),
        ft.Row([adm_txt_user, adm_txt_email, adm_txt_pass], alignment="center"),
        ft.Row([adm_cb_admin, adm_cb_rep, adm_cb_bal], alignment="center"),
        adm_btn_save,
        ft.Container(content=users_list_view, border=ft.border.all(1, "#ddd"), border_radius=5, padding=5)
    ], visible=False, horizontal_alignment="center", spacing=5)

    screen_settings = ft.Container(visible=False, expand=True, content=ft.Column([
        ft.Row([ft.IconButton( ft.icons.ARROW_BACK, on_click=lambda _: toggle_settings(None)), ft.Text("⚙️ الإعدادات", size=20, weight="bold")]),
        password_section, 
        admin_panel,      
        ft.Divider(),
        ft.ListTile(leading=ft.Text("🎙️", size=20), title=ft.Text("أوامر ريكو الصوتية"), on_click=lambda _: open_dictionary_screen()),
    ], scroll=ft.ScrollMode.AUTO, horizontal_alignment="center"))

    screen_dictionary = ft.Container(visible=False, expand=True, content=ft.Column([
        ft.Row([ft.IconButton( ft.icons.ARROW_BACK, on_click=lambda _: nav_to_settings()), ft.Text("🎙️ قاموس ريكو", size=18, weight="bold")], alignment=ft.MainAxisAlignment.CENTER),
        ft.Container(
            content=ft.Row([
                ft.Text("الكلمة (الدلع)", width=110, text_align="center", weight="bold", color="grey"),
                ft.Text("المعنى (الأصل)", width=110, text_align="center", weight="bold", color="grey"),
                ft.Text("النوع", width=120, text_align="center", weight="bold", color="grey"),
                ft.Container(width=40)
            ], alignment=ft.MainAxisAlignment.CENTER, spacing=5),
            padding=5, bgcolor="#f0f0f0", border_radius=5
        ),
        control_list_view,
        ft.Divider(),
        ft.Row([
            ft.ElevatedButton("➕ إضافة", on_click=lambda _: add_dictionary_row(), bgcolor="#1976D2", color="white"),
            ft.ElevatedButton("💾 حفظ التغييرات", on_click=lambda _: save_control_to_sheet_logic(), bgcolor="green", color="white")
        ], alignment=ft.MainAxisAlignment.CENTER, spacing=20)
    ], horizontal_alignment=ft.CrossAxisAlignment.CENTER))

    def open_dictionary_screen():
        screen_settings.visible = False; screen_dictionary.visible = True
        app_state["current_page"] = "settings"
        control_list_view.controls.clear()
        for kw, mv in control_dict["synonyms"].items(): add_dictionary_row(kw, mv, "Entity")
        for kw, mv in control_dict["nav"].items(): add_dictionary_row(kw, mv, "Nav")
        for kw, mv in control_dict["defaults"].items(): add_dictionary_row(kw, mv, "Payment")
        page.update()

    def nav_to_settings():
        screen_dictionary.visible = False; screen_settings.visible = True; page.update()

    def toggle_settings(e):
        is_visible = screen_settings.visible
        screen_register.visible = False; screen_balances.visible = False; screen_transactions.visible = False; screen_reports.visible = False; screen_cash_counting.visible = False; screen_dictionary.visible = False; screen_settings.visible = False
        if not is_visible:
            screen_settings.visible = True
            app_state["current_page"] = "settings"
            
            try:
                with open(resource_path("users_db.json"), "r", encoding="utf-8") as f: db = json.load(f)
                txt_my_user.value = app_state["user_name"]
                txt_my_email.value = db.get(app_state["user_name"], {}).get("email", "")
            except: pass
            
            if app_state.get("user_role") == "admin":
                admin_panel.visible = True
                load_users_table()
                adm_on_user_change(None) 
            else:
                admin_panel.visible = False
        else:
            screen_register.visible = True
            app_state["current_page"] = "reg"
            btn_nav_reg.bgcolor = "#424242"; btn_nav_reg.color = "white"
        page.update()

    # --- Navigation ---
    def nav_click(e):
        screen_register.visible = False; screen_balances.visible = False; screen_transactions.visible = False; screen_reports.visible = False; screen_cash_counting.visible = False; screen_settings.visible = False; screen_dictionary.visible = False
        btn_nav_reg.bgcolor = "#eeeeee"; btn_nav_reg.color = "black"; btn_nav_bal.bgcolor = "#eeeeee"; btn_nav_bal.color = "black"; btn_nav_trans.bgcolor = "#eeeeee"; btn_nav_trans.color = "black"; btn_nav_reports.bgcolor = "#eeeeee"; btn_nav_reports.color = "black"; btn_nav_cash.bgcolor = "#eeeeee"; btn_nav_cash.color = "black"
        
        if isinstance(e, ft.Control): sender = e
        elif hasattr(e, "control"): sender = e.control
        else: sender = btn_nav_reg 
        sender.bgcolor = "#424242"; sender.color = "white"
        
        app_state["current_page"] = sender.data 
        
        if sender.data == "reg": screen_register.visible = True
        elif sender.data == "bal": 
            screen_balances.visible = True
            update_balances_view_ui()
            trigger_refresh_thread()

        elif sender.data == "trans": 
            screen_transactions.visible = True
            update_balances_view_ui()
            trigger_refresh_thread()

        elif sender.data == "reports": 
            screen_reports.visible = True
            update_report_view()
        elif sender.data == "cash": 
            screen_cash_counting.visible = True
            if cash_state["current_safe_name"] == "الكل":
                btn_select_safe.text = "الكل"
                calc_cash_logic()
        page.update()

    btn_nav_reg = ft.ElevatedButton("تسجيل", data="reg", on_click=nav_click, bgcolor="#424242", color="white", expand=True, style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=0), padding=0))
    btn_nav_bal = ft.ElevatedButton("أرصدة", data="bal", on_click=nav_click, bgcolor="#eeeeee", color="black", expand=True, style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=0), padding=0))
    btn_nav_trans = ft.ElevatedButton("عمليات", data="trans", on_click=nav_click, bgcolor="#eeeeee", color="black", expand=True, style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=0), padding=0))
    btn_nav_reports = ft.ElevatedButton("تقارير", data="reports", on_click=nav_click, bgcolor="#eeeeee", color="black", expand=True, style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=0), padding=0))
    btn_nav_cash = ft.ElevatedButton("جرد نقدية", data="cash", on_click=nav_click, bgcolor="#eeeeee", color="black", expand=True, style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=0), padding=0))
    nav_bar = ft.Row([btn_nav_reg, btn_nav_bal, btn_nav_trans, btn_nav_reports, btn_nav_cash], alignment="center", spacing=0)

    def show_app_screen():
        page.clean(); page.vertical_alignment = ft.MainAxisAlignment.START; user = app_state["user_name"]
        
        # تعريف زر الإعدادات هنا قبل الاستخدام (إصلاح NameError)
        settings_btn = ft.IconButton( ft.icons.SETTINGS, on_click=toggle_settings) 
        
        populate_entity_dropdown() 
        page.add(ft.Column([
            ft.Container(height=5), 
            ft.Row([ft.Text(f"👤 {user}", weight="bold", size=16), settings_btn], alignment="space_between"), 
            ft.Divider(), 
            nav_bar, 
            ft.Divider(height=1), 
            ft.Container(content=ft.Stack([screen_register, screen_balances, screen_transactions, screen_reports, screen_cash_counting, screen_settings, screen_dictionary]), expand=True), 
            # --- تعديل الترتيب لإظهار الشاشة السفلية ---
            audio_bottom_bar, # شريط الصوت
            ft.Divider(height=1), 
            log_container # شاشة اللوج أسفله
            # ---------------------------------------------
        ], horizontal_alignment="center", expand=True))

# --- لوحة الإدارة ---

    # --- الإعداد لأول مرة ---
    setup_url = ft.TextField(label="رابط Google Sheet", width=300)
    def finish_setup(e):
        if not setup_url.value: return
        with open(resource_path("app_config.json"), "w") as f: json.dump({"sheet_url": encode_base64(setup_url.value)}, f)
        with open(resource_path("users_db.json"), "w") as f: json.dump({"admin": {"pass": encode_base64("admin"), "role": "admin", "reports": True, "balances": True}}, f)
        screen_setup.visible = False; screen_login.visible = True; page.update()
        
    screen_setup = ft.Container(visible=False, content=ft.Column([ft.Text("إعداد ريكو لأول مرة", size=20, weight="bold"), setup_url, ft.ElevatedButton("إنهاء", on_click=finish_setup)], horizontal_alignment="center"))

# --- تسجيل الدخول ---
    login_error_txt = ft.Text("", color="red", size=13, weight="bold", visible=False)
    
    def send_recovery_email(e):
        u = log_u.value.strip()
        if not u:
            login_error_txt.value = "⚠️ اكتب اسم المستخدم في الخانة أولاً لنرسل لك الباسورد"
            login_error_txt.color = "orange"; login_error_txt.visible = True; login_error_txt.update(); return
            
        if not check_internet():
            login_error_txt.value = "❌ لا يوجد إنترنت. انتظر حتى تتصل بالشبكة وحاول مجدداً"
            login_error_txt.color = "red"; login_error_txt.visible = True; login_error_txt.update(); return

        try:
            with open(resource_path("users_db.json"), "r", encoding="utf-8") as f: db = json.load(f)
            if u not in db:
                login_error_txt.value = "❌ المستخدم غير موجود في النظام"
                login_error_txt.color = "red"; login_error_txt.visible = True; login_error_txt.update(); return
                
            user_email = db[u].get("email", "")
            if not user_email:
                login_error_txt.value = "❌ لا يوجد بريد إلكتروني مسجل لهذا الحساب"
                login_error_txt.color = "red"; login_error_txt.visible = True; login_error_txt.update(); return

            user_pass = decode_base64(db[u]["pass"])
            
            # --- إعدادات الإرسال (يجب تغييرها ببياناتك لاحقاً) ---
            SENDER_EMAIL = "mohammedmanaa2803@gmail.com"
            APP_PASSWORD = "rynoquhrgaxdfryc" 
            # ----------------------------------------------
            
            msg = MIMEText(f"مرحباً {u}،\n\nكلمة المرور الخاصة بك في تطبيق ريكو هي: {user_pass}\n\nيرجى المحافظة عليها سراً.")
            msg['Subject'] = 'استعادة كلمة المرور - تطبيق ريكو'
            msg['From'] = SENDER_EMAIL
            msg['To'] = user_email

            login_error_txt.value = "⏳ جاري إرسال الإيميل..."; login_error_txt.color = "blue"
            login_error_txt.visible = True; login_error_txt.update()
            
            server = smtplib.SMTP('smtp.gmail.com', 587)
            server.starttls()
            server.login(SENDER_EMAIL, APP_PASSWORD)
            server.send_message(msg)
            server.quit()
            
            login_error_txt.value = f"✅ تم إرسال كلمة المرور بنجاح إلى إيميلك"
            login_error_txt.color = "green"; login_error_txt.visible = True; login_error_txt.update()
        except Exception as ex:
            login_error_txt.value = "❌ فشل الإرسال، تأكد من إعدادات السيرفر أو كلمة المرور"
            login_error_txt.color = "red"; login_error_txt.visible = True; login_error_txt.update()

    def do_login(e=None):
        u = log_u.value.strip(); p = log_p.value.strip()
        if not u or not p:
            login_error_txt.value = "❌ يرجى إدخال اسم المستخدم وكلمة المرور"; login_error_txt.color = "red"
            login_error_txt.visible = True; login_error_txt.update(); return
            
        if not os.path.exists(resource_path("users_db.json")): return
        try:
            with open(resource_path("users_db.json"), "r", encoding="utf-8") as f: db = json.load(f)
            if u in db and decode_base64(db[u]["pass"]) == p:
                login_error_txt.visible = False
                app_state["user_name"] = u; app_state["user_role"] = db[u].get("role", "user")
                if log_rem.value:
                    with open(resource_path("session.json"), "w") as f: json.dump({"u": encode_base64(u), "p": encode_base64(p)}, f)
                show_main_app()
            else: 
                login_error_txt.value = "❌ اسم المستخدم أو كلمة المرور غير صحيحة"; login_error_txt.color = "red"
                login_error_txt.visible = True; login_error_txt.update()
        except Exception as ex:
            login_error_txt.value = "❌ خطأ في قراءة البيانات"; login_error_txt.color = "red"
            login_error_txt.visible = True; login_error_txt.update()

    log_u = ft.TextField(label="المستخدم", width=250, on_submit=do_login)
    log_p = ft.TextField(label="كلمة المرور", password=True, width=250, on_submit=do_login)
    log_rem = ft.Checkbox(label="تذكرني", value=False)
    btn_forgot = ft.TextButton("نسيت كلمة المرور؟", on_click=send_recovery_email) # الزرار الجديد

    screen_login = ft.Container(visible=False, content=ft.Column([
        ft.Container(height=40),
        ft.Text("تسجيل الدخول", size=26, weight="bold", color="#1565C0"), 
        login_error_txt, 
        log_u, 
        log_p, 
        ft.Row([
            ft.ElevatedButton("دخول", on_click=do_login, width=120, height=45, bgcolor="#1565C0", color="white"), 
            log_rem
        ], alignment=ft.MainAxisAlignment.CENTER, spacing=15),
        btn_forgot # ضفناه في الشاشة هنا
    ], horizontal_alignment="center"))

    screen_splash = ft.Container(visible=True, content=ft.Column([ft.ProgressRing(), ft.Text("جاري الفحص...")], horizontal_alignment="center"))

    # --- عرض التطبيق الأساسي ---
# --- عرض التطبيق الأساسي ---
    def show_main_app():
        page.clean()
        page.vertical_alignment = ft.MainAxisAlignment.START
        page.floating_action_button.visible = True
        
        # هنا بنعرف زرار الترس
        settings_btn = ft.IconButton( ft.icons.SETTINGS, on_click=toggle_settings) 
        
        page.add(ft.Column([
            # هنا ضفنا الزرار جنب اسم المستخدم وخلينا بينهم مسافة
            ft.Row([ft.Text(f"👤 {app_state['user_name']}", weight="bold"), settings_btn], alignment=ft.MainAxisAlignment.SPACE_BETWEEN), 
            nav_bar, ft.Divider(height=1),
            ft.Container(content=ft.Stack([screen_register, screen_balances, screen_transactions, screen_reports, screen_cash_counting, screen_settings, screen_dictionary]), expand=True),
            rico_subtitle, audio_bottom_bar, ft.Divider(height=1), log_container
        ], horizontal_alignment="center", expand=True))
        
        nav_click(type("", (), {"control": type("", (), {"data": "reg"})()})())
        check_sync_status()
        
# --- سحر الترحيب الذكي (تحديد الجنس + رسائل عشوائية) ---
        def delayed_welcome():
            import time
            import random
            time.sleep(3)  # نأخر النطق 3 ثواني
            full_name = app_state['user_name'].strip()
            name_parts = full_name.split()
            if len(name_parts) > 1 and name_parts[0] == "عبد":
                first_name = name_parts[0] + " " + name_parts[1]
            else:
                first_name = name_parts[0] if name_parts else full_name
            
            # 1. تنظيف الاسم من أي مسافات
            clean_name = first_name.replace("ْ", "").strip()

            # 2. قائمة بأسماء الإناث
            female_names = [
                "سحر", "فاطمة", "مروة", "عائشة", "منى", "مريم", "لوجينا", "نادين", "لين", "نور", "هبة", 
                "شيماء", "ريهام", "دينا", "ياسمين", "سارة", "هاجر", "فريده", "ندى", 
                "آية", "إيمان", "دعاء", "أميرة", "نجلاء", "هدى", "سمية"
            ]
            
            # 3. نطق الترحيب العشوائي بناءً على الجنس
            spoken_name = clean_name + "ْ" # إضافة السكون للنطق الصحيح
            
            if clean_name in female_names:
                # رسائل ترحيب الإناث
                f_welcomes = [
                    f"أَهْلاً بِكِ يَا {spoken_name}، كَيْفَ أُسَاعِدُكِ؟",
                    f"يَا مَرْحَباً يَا {spoken_name}، أَنَا جَاهِز لِتَسْجِيلِ حِسَابَاتِكِ.",
                    f"نَوَّرْتِي الْبَرْنامَج يَا {spoken_name}، أُسَاعِدُكِ فِي إِيه الْيَوْم؟",
                    f"أَهْلاً يَا {spoken_name}، تَحْت أَمْرِكِ فِي أَيِّ وَقْت."
                ]
                speak(random.choice(f_welcomes))
            else:
                # رسائل ترحيب الذكور
                m_welcomes = [
                    f"أَهْلاً بِكَ يَا {spoken_name}، كَيْفَ أُسَاعِدُكْ؟",
                    f"يَا مَرْحَباً بِكَ يَا {spoken_name}، جَاهِز لِتَسْجِيلِ حِسَابَاتَكْ.",
                    f"نَوَّرْت الْبَرْنامَج يَا {spoken_name}، ٍتَحْت أَمْرَكْ يَا غَالِي.",
                    f"أَهْلاً يَا {spoken_name}، نَبْدَأ الشُّغْل , مِن أَين نَبْداءْ ؟"
                ]
                speak(random.choice(m_welcomes))

        import threading
        threading.Thread(target=delayed_welcome, daemon=True).start()

    # فحص البداية
    def init_check():
        time.sleep(1)
        if not check_internet(): app_state["is_offline"] = True; add_log("أوفلاين", "orange")
        if not os.path.exists(resource_path("app_config.json")): screen_splash.visible = False; screen_setup.visible = True; page.update(); return
        if os.path.exists(resource_path("session.json")):
            try:
                with open(resource_path("session.json"), "r") as f: s = json.load(f); log_u.value = decode_base64(s["u"]); log_p.value = decode_base64(s["p"]); do_login(); return
            except: pass
        screen_splash.visible = False; screen_login.visible = True; page.update()

    page.add(ft.Stack([screen_splash, screen_setup, screen_login], expand=True))
    threading.Thread(target=init_check, daemon=True).start()
    threading.Thread(target=load_data_background, daemon=True).start()
    threading.Thread(target=listen_background, daemon=True).start()

    def app_loop():
        # --- إضافة الانتظار البسيط هنا لحل مشكلة عدم التشغيل الفوري ---
        time.sleep(0.5) 
        # -------------------------------------------------------------
        start_time = time.time(); last_entity = None; last_main = None; last_sub = None; last_type = None; data_loaded_flag = False
        while True:
            try:
                # --- شرط الخروج الآمن (المعدل والمبسط) ---
                # REMOVED the safety check that was killing the loop prematurely
                # if not header_txt.page: break  <-- THIS WAS THE CULPRIT
                
                # --- 1. تحديث العداد (الوقت) ---
                elapsed = time.time() - start_time; h, m, s = int(elapsed//3600), int((elapsed%3600)//60), int(elapsed%60)
                timer_lbl.value = f"⏱️ {h:02}:{m:02}:{s:02}"
                try: timer_lbl.update()
                except: pass
                
                # --- 2. (التعديل هنا) تحديث حالة التحميل لحظياً ---
                # بنقارن النص اللي على الشاشة بالنص اللي في الذاكرة، لو مختلف نحدثه فوراً
                if header_txt.value != app_state["header_text"]:
                    header_txt.value = app_state["header_text"]
                    try:
                        header_txt.update()
                        # إذا كنا في شاشة الدخول (لم يتم تحديد مستخدم بعد)، نحدث الصفحة بالكامل لضمان الظهور
                        if not app_state["user_name"]:
                            page.update()
                    except: pass

                if header_txt.color != app_state["header_color"]:
                    header_txt.color = app_state["header_color"]
                    try: header_txt.update()
                    except: pass
                
# --- 3. تشغيل الدوال بعد اكتمال التحميل ---
                if app_state["data_ready"] and not data_loaded_flag:
                    populate_entity_dropdown()
                    trigger_refresh_thread()
                    data_loaded_flag = True
                    add_log("✅ تحديث البيانات الأول", "green")
                    
                    if not app_state.get("is_offline"):
                        off_c = get_offline_count()
                        if off_c > 0:
                            dlg_offline_action.content.value = f"لقد قمت بتسجيل ({off_c}) عمليات أثناء عدم الاتصال.\nماذا تريد أن تفعل بها؟"
                            dlg_offline_action.open = True
                            try: page.update()
                            except: pass
                # --- 4. أنيميشن الموجات الصوتية ---
                try:
                    if volume_bar.page:
                        if app_state["mic_status"] == "listening":
                            new_w = random.randint(20, 300)
                            volume_bar.width = new_w
                            volume_bar.bgcolor = "#E91E63" 
                            volume_bar.update()
                        elif app_state["mic_status"] == "processing":
                            volume_bar.width = 300
                            volume_bar.bgcolor = "orange" 
                            volume_bar.update()
                        else: # idle
                            if volume_bar.width > 0:
                                volume_bar.width = 0 
                                volume_bar.bgcolor = "grey"
                                volume_bar.update()
                except: pass
                # ----------------------------

                # --- 5. تحديث حالة الواجهة (UI State Updates) ---
                current_type = get_current_value(dd_type, txt_type)
                if current_type != last_type:
                    last_type = current_type
                    if current_type == "تحويل داخلي":
                        dd_main.options = [ft.dropdown.Option("تحويلات داخلية")]; dd_main.value = "تحويلات داخلية"; dd_main.disabled = True; dd_main.label = "التصنيف الرئيسي (مثبت)"
                        if txt_main.visible: toggle_control_logic(dd_main, txt_main, btn_main)
                        entities = list(PAYMENT_OPTS.keys()); dd_sub.options = [ft.dropdown.Option(e) for e in entities]; dd_sub.value = None; dd_sub.label = "إلى (الكيان المحول إليه)"; dd_sub.toggle_btn.visible = True; dd_sub.toggle_btn.tooltip = "إضافة كيان جديد"; dd_main.toggle_btn.visible = False
                    elif current_type == "تحويل عهدة":
                        dd_main.options = [ft.dropdown.Option("تحويلات عهدة")]; dd_main.value = "تحويلات عهدة"; dd_main.disabled = True; dd_main.label = "التصنيف الرئيسي (مثبت)"
                        if txt_main.visible: toggle_control_logic(dd_main, txt_main, btn_main)
                        all_safes = []; 
                        for safes in PAYMENT_OPTS.values(): all_safes.extend(safes)
                        unique_safes = sorted(list(set(all_safes))); dd_sub.options = [ft.dropdown.Option(s) for s in unique_safes]; dd_sub.value = None; dd_sub.label = "إلى (الخزنة المحول إليها)"; dd_sub.toggle_btn.visible = True; dd_sub.toggle_btn.tooltip = "إضافة خزنة جديدة"; dd_main.toggle_btn.visible = False
                    else:
                        dd_main.disabled = False; dd_main.label = "التصنيف الرئيسي"; dd_sub.label = "التصنيف الفرعي"; dd_main.toggle_btn.visible = True; dd_sub.toggle_btn.visible = True
                        current_entity = get_current_value(dd_entity, txt_entity); update_dropdowns_logic(current_entity, None)
                    try: dd_main.update(); dd_sub.update(); dd_main.toggle_btn.update(); dd_sub.toggle_btn.update()
                    except: pass

                current_entity = get_current_value(dd_entity, txt_entity)
                if current_entity != last_entity:
                    last_entity = current_entity
                    if current_type not in ["تحويل داخلي", "تحويل عهدة"]:
                        update_dropdowns_logic(current_entity, None); dd_sub.value = None
                        try: dd_sub.update() 
                        except: pass

                current_main = get_current_value(dd_main, txt_main)
                if current_main != last_main:
                    last_main = current_main
                    if current_type not in ["تحويل داخلي", "تحويل عهدة"]: update_dropdowns_logic(current_entity, current_main)

                current_sub = get_current_value(dd_sub, txt_sub)
                if current_sub != last_sub:
                    last_sub = current_sub
                    if current_sub and "بنزين" in current_sub and current_type not in ["تحويل داخلي", "تحويل عهدة"]: cb_gas_split.visible = True
                    else: cb_gas_split.visible = False; cb_gas_split.value = False
                    try: cb_gas_split.update()
                    except: pass

                # --- 6. معالجة الأوامر الصوتية ---
                if app_state["last_command"]:
                    raw_text = app_state["last_command"]
                    app_state["last_command"] = ""
                    app_state["voice_mode"] = True
                    

                    try:
                        # --- سحر الدردشة والذكاء الاجتماعي (مع الفرامل القاطعة) ---
                        # قائمة المحظورات (الدردشة) الشاملة لمنع التداخل مع المحلل الذكي
                        social_words = [
                            # السلام عليكم بكافة أشكالها
                            "السلام عليكم", "سلام عليكم", "السلام عليك", "سلام عليك", 
                            
                            # تحيات الصباح والمساء
                            "صباح الخير", "صباح النور", "صباح الفل", "صباح الورد",
                            "مساء الخير", "مساء النور", "مساء الفل", "مساء الورد",
                            
                            # السؤال عن الحال (بمختلف الإملاءات)
                            "عامل ايه", "عامل إيه", "عامل اية", "عامل إية", 
                            "ازيك", "إزيك", "اخبارك", "أخبارك", "كيف حالك", 
                            
                            # الترحيب
                            "مرحبا", "مرحباً", "هلا والله", "يا هلا", "هلا",
                            
                            # السؤال عن الهوية
                            "اسمك ايه", "إسمك إيه", "اسمك اية", "إسمك اية", 
                            "مين انت", "مين إنت", "انت مين", "إنت مين", 
                            "من انت", "من إنت"
                        ]
                                # الفحص الأولي السريع: لو الكلام دردشة من القائمة اللي إنت تعبت فيها
                        is_chat = any(word in raw_text for word in social_words)
                        
                        if is_chat:
                            # تحديث الواجهة فوراً لمسح أي رسائل قديمة أو "لم أفهم"
                            app_state["header_text"] = "💬 دردشة ذكية..."
                            if header_txt.page: header_txt.update()
                            
                            # 1. إلقاء السلام (بنفس نطقك وتشكيلك)
                            salam_words = ["السلام عليكم", "سلام عليكم", "السلام عليك", "سلام عليك"]
                            if any(word in raw_text for word in salam_words):
                                speak("وَعَلَيْكُمُ السَّلام وَرَحْمَةُ اللَّهْ وَبَرَكَاتُهْ. أَقْدَر أُسَاعِدْ فِي إِيه؟")
                            
                            # 2. تحيات الصباح
                            elif any(word in raw_text for word in ["صباح الخير", "صباح النور", "صباح الفل", "صباح الورد"]):
                                import random
                                m_replies = [
                                    "صَبَاح النُّور، أَقْدَر أُسَاعِدْ فِي إِيه؟",
                                    "صَبَاح الْفُل وَالْيَاسْمِينْ، نَبْدَأ الشُّغْل؟",
                                    "صَبَاح الْوَرْد، جَاهِز لِتَسْجِيل حِسَابَاتَكْ!"
                                ]
                                speak(random.choice(m_replies))

                            # 3. تحيات المساء
                            elif any(word in raw_text for word in ["مساء الخير", "مساء النور", "مساء الفل", "مساء الورد"]):
                                import random
                                e_replies = [
                                    "مَسَاء النُّور، أَقْدَر أُسَاعِدْ فِي إِيه؟",
                                    "مَسَاء الْفُل وَالْيَاسْمِينْ، تَحْت أَمْرَكْ.",
                                    "مَسَاء الْوَرْد، نُسَجِّل إِيه دِلْوَقْتِي؟"
                                ]
                                speak(random.choice(e_replies))

                            # 4. الدردشة (عامل إيه / إزيك / هلا)
                            elif any(word in raw_text for word in ["عامل ايه", "عامل إيه", "ازيك", "هلا والله", "يا هلا", "إزيك", "اخبارك", "كيف حالك"]):
                                import random
                                replies = [
                                    "الْحَمْدُ لِلَّه تَمَامْ، فِي عَمَلِيَّة جَدِيدَة هَنُسَجِّلُهَا؟",
                                    "أَنَا بِخَيْر طُول مَا حِسَابَاتَك مَظْبُوطَة! أَسَاعِدَكْ فِي إِيه؟",
                                    "تَمَامْ جِدًّا! أَنَا جَاهِزْ لِتَسْجِيلِ مَصَارِيفَكْ.",
                                    "بِخَيْر الْحَمْدُ لِلَّه، نَبْدَأ الشُّغْلْ؟"
                                ]
                                speak(random.choice(replies))

                            # 5. الهوية
                            elif any(word in raw_text for word in ["اسمك", "مين انت", "انت مين"]):
                                import random
                                identity_replies = [
                                    "أَنَا رِيكُو، مُسَاعِدَكْ الشَّخْصِي الْمُبَرْمَج مَخْصُوص لِتَسْجِيل حِسَابَاتَكْ. وَاللِّي بَرْمَجْنِي الْمُهَنْدِس مُحَمَّد مَنَّاعْ.",
                                    "إِسْمِي رِيكُو! وَظِيفَتِي أَسَاعِدَكْ فِي تَسْجِيل مَصَارِيفَكْ وَحِسَابَاتَك بِسُهُولَة، وَتَمَّتْ بَرْمَجَتِي بِوَاسِطَةِ الْمُهَنْدِس مُحَمَّد مَنَّاعْ."
                                ]
                                speak(random.choice(identity_replies))

                            # الفرامل القاتلة: بنقول للكود ارجع للبداية وما تنفذش أي حاجة تحت (زي المحلل الذكي)
                            app_state["mic_status"] = "idle"
                            app_state["voice_mode"] = False
                            continue 

                        # --- منطقة الأوامر المالية (لن يصل إليها الكود إذا كان الكلام دردشة) ---
                       
                        parsed = smart_parser(raw_text)
                        intent = parsed["intent"]
                        data = parsed["data"]
                        
                        parsed = smart_parser(raw_text)
                        intent = parsed.get("intent")
                        data = parsed.get("data")

        # --- كوبري التنقل الإجباري (يفرض سيطرته على المترجم) ---
                        txt_check = raw_text.strip()
                        
                        # 1. الجرد والنقدية والخزنة
                        if txt_check in [
                            "الجرد", "جرد", "افتح الجرد", "نقدية", "النقدية", "نقديه", "النقديه", 
                            "جرد نقدية", "جرد النقدية", "الفلوس", "عد الفلوس", "هانعد فلوس", 
                            "عد النقديه", "فلوس", "الخزنة", "خزنة", "افتح الخزنة", "الخزينه", 
                            "خزينه", "الدرج", "الكاش", "كاش", "احسب الفلوس"
                        ]:
                            intent = "navigate"
                            data = "cash"
                            
                        # 2. التقارير والملخصات
                        elif txt_check in [
                            "التقارير", "تقارير", "افتح التقارير", "تقرير", "هات التقارير", 
                            "عرض التقارير", "الملخص", "ملخص", "كشف حساب", "الريبورت"
                        ]:
                            intent = "navigate"
                            data = "reports"
                            
                        # 3. العمليات والحركات
                        elif txt_check in [
                            "العمليات", "عمليات", "افتح العمليات", "العمليه", "العملية", 
                            "الحركات", "حركات", "الحركه", "حركة", "سجل العمليات", 
                            "المعاملات", "معاملات", "هات العمليات",
                            "أخر عمليه", "اخر عمليه", "أخر عملية", "اخر عملية",
                            "هات أخر عمليه", "هات اخر عمليه", "هات أخر عملية", "هات اخر عملية",
                            "اخر حركه", "أخر حركه", "هات اخر حركه", "هات أخر حركه" 
                            "وريني أخر عمليه", "وريني اخر عمليه", "وريني أخر عملية", "وريني اخر عملية",
                            "وريني اخر حركه", "وريني أخر حركه" 
                        ]:
                            intent = "navigate"
                            data = "trans"
                            
                        # 4. الأرصدة (ومعانا كام)
                        elif txt_check in [
                            "الأرصدة", "أرصدة", "ارصدة", "الارصده", "ارصده", "افتح الأرصدة", 
                            "رصيد", "الرصيد", "رصيدي", "معايا كام", "باقي كام", "الحسابات", "حسابات"
                        ]:
                            intent = "navigate"
                            data = "bal"
                            
                        # 5. التسجيل والعودة للرئيسية
                        elif txt_check in [
                            "التسجيل", "تسجيل", "الرئيسيه", "الرئيسية", "افتح التسجيل", 
                            "الصفحة الرئيسية", "الصفحه الرئيسيه", "سجل", "عملية جديدة", 
                            "فاتورة جديدة", "الهوم", "رجوع"
                        ]:
                            intent = "navigate"
                            data = "reg"

                        if intent == "stop_listening":
                            app_state["mic_status"] = "idle"
                            app_state["header_text"] = "💤 في وضع الصمت"; app_state["header_color"] = "grey"
                            if header_txt.page: header_txt.update()
                            speak("تمامْ، هاسكتْ")
                            continue 

                        if intent == "navigate":
                            # 1. المترجم الذكي: تحويل الكلمة العربي للكود البرمجي بتاعك
                            target_data = str(data)
                            if "تسجيل" in target_data: 
                                target_data = "reg"
                            elif "تقارير" in target_data or "تقرير" in target_data or "التقارير" in target_data: 
                                target_data = "reports"  # السر كان هنا (reports بدل rep)
                            elif "رصيد" in target_data or "ارصدة" in target_data or "أرصدة" in target_data or "الأرصده" in target_data or "الارصده" in target_data or "الارصدة" in target_data or "الأرصدة" in target_data or "الرصيد" in target_data: 
                                target_data = "bal"
                            elif "عمليات" in target_data or "العمليات" in target_data or "أخر عمليه" in target_data or "اخر عمليه" in target_data: 
                                target_data = "trans"
                            elif "جرد" in target_data or "نقدية" in target_data or "عد النقديه" in target_data or "الفلوس" in target_data or "الجرد" in target_data or  "عد فلوس" in target_data or "هانعد فلوس" in target_data: 
                                target_data = "cash"
                            
                            # 2. إرسال الكود الصحيح لدالة الانتقال
                            nav_click(type("", (), {"control": type("", (), {"data": target_data})()})())
                            
                            # 3. تحديث الواجهة الإجباري
                            if header_txt.page: 
                                header_txt.page.update()
                                
                            speak("تَمَّ الْفَتْح")

                        elif intent == "cancel":
                            cancel_operation()
                        elif intent == "close_dialog":
                            if dlg_box_details.open: close_box_dlg()
                            elif dlg_choice.open: close_choice_dlg()
                            speak("تمامْ")
                        elif intent == "save_transaction":
                            save_data()
                        elif intent == "select_safe":
                            if btn_select_safe.page:
                                btn_select_safe.text = data
                                btn_select_safe.update()
                            on_safe_changed(data)
                            speak(f"تم اختيار خزنة {data}")
                        elif intent == "update_cash":
                            d_val = data["denom"]
                            d_count = data["count"]
                            if d_val in cash_inputs:
                                cash_inputs[d_val].value = str(d_count)
                                if cash_inputs[d_val].page: cash_inputs[d_val].update()
                                calc_cash_logic()
                                speak(f"تمامْ.. {d_count} ورقة من فئة {d_val}")
                        elif intent == "show_details":
                            target = data
                            temp_bal = 0
                            temp_details = {}
                            for r in raw_data:
                                if len(r)>8 and r[5] == target:
                                     amt = float(r[1])
                                     if r[8] in ["مصروف"]: temp_bal -= amt
                                     else: temp_bal += amt
                                     safe = r[6]
                                     temp_details[safe] = temp_details.get(safe, 0) + amt 
                            if temp_bal == 0 and not temp_details:
                                speak(f"لا توجد تفاصيل لكيانْ {target}")
                            else:
                                fake_e = type("", (), {"control": type("", (), {"data": {"name": target, "total": temp_bal, "breakdown": temp_details}})()})()
                                on_box_click(fake_e)
                                speak(f"تفاصيل {target}")

                        elif intent == "fill_form":
                            p_data = data
                            if p_data["amount"]:
                                txt_amount.value = p_data["amount"]
                                if txt_amount.page: txt_amount.update()
                                
                            if p_data["entity"]:
                                dd_entity.value = p_data["entity"]
                                if dd_entity.page: dd_entity.update()
                                update_dropdowns_logic(p_data["entity"], None)
                                
                            if p_data["type"]:
                                dd_type.value = p_data["type"]
                                if dd_type.page: dd_type.update()
                                
                            if p_data["main"]:
                                dd_main.value = p_data["main"]
                                if dd_main.page: dd_main.update()
                                update_dropdowns_logic(p_data["entity"], p_data["main"])
                                
                            if p_data["payment"]:
                                dd_payment.value = p_data["payment"]
                                if dd_payment.page: dd_payment.update()
                                
# --- 1. الحل الجذري لاختيار التصنيف الفرعي (النسخة المدرعة) ---
                            time.sleep(0.1)  # إعطاء فرصة للقوائم الفرعية تتحدث
                            
                            final_sub = ""
                            current_options = [opt.key for opt in dd_sub.options]
                            
                            target_sub = p_data.get("sub")
                            if not target_sub:
                                target_sub = p_data.get("details", "")
                                
                            if target_sub:
                                target_sub = str(target_sub).strip()
                                matched = False
                                
                                # تطابق ذكي: هل الخيار (شيبسي) موجود جوه الكلام اللي قلناه (30 شيبسي)؟
                                for opt in current_options:
                                    if opt == target_sub or opt in target_sub or target_sub in opt:
                                        dd_sub.value = opt
                                        final_sub = opt
                                        matched = True
                                        break
                                
                                # لو ملقاش تطابق صريح، يلجأ للبحث التقريبي كخطة بديلة
                                if not matched:
                                    best_match = fuzzy_match(target_sub, current_options, cutoff=0.4)
                                    if best_match:
                                        dd_sub.value = best_match
                                        final_sub = best_match
                                        
                                if dd_sub.page: dd_sub.update()
                                
                            # --- 2. تنسيق خانة التفاصيل (المبلغ + جنيه + التصنيف) ---
                            amount_val = p_data.get('amount')
                            if amount_val:
                                sub_for_details = final_sub if final_sub else target_sub
                                
                                # عشان لو كلمة شيبسي موجودة ميكتبهاش مرتين
                                clean_details = str(sub_for_details).replace(str(amount_val), "").strip()
                                txt_details.value = f"{amount_val} جنيه {clean_details}".strip()
                            else:
                                txt_details.value = target_sub
                            
                            if txt_details.page: txt_details.update()

                            # --- 3. كوبري اختيار التصنيف الفرعي المتأخر (الضربة القاضية) ---
                            def force_sub_select():
                                import time
                                time.sleep(1)  # نستنى ثانية كاملة لحد ما القوائم تتحدث براحتها
                                current_opts = [opt.key for opt in dd_sub.options]
                                target_s = p_data.get("sub") or p_data.get("details", "")
                                target_s = str(target_s).strip()
                                if target_s:
                                    for opt in current_opts:
                                        if opt == target_s or opt in target_s or target_s in opt:
                                            dd_sub.value = opt
                                            if dd_sub.page: dd_sub.update()
                                            break
                            import threading
                            threading.Thread(target=force_sub_select, daemon=True).start()

                            # نطق كلمة (تَمَامْ) بالسكون عشان ميمطش فيها
                            speak(f"تَمَامْ.. {amount_val if amount_val else ''} {p_data.get('details', '')}")
                            
                            if "سجل" not in raw_text and "احفظ" not in raw_text:
                                app_state["header_text"] = "🤔 تمام.. أسجل؟"; app_state["header_color"] = "#E65100"
                                if header_txt.page:
                                    header_txt.value = app_state["header_text"]; header_txt.color = app_state["header_color"]; header_txt.update()
                        elif intent == "new_category_error":
                            speak("هل هذا تصنيف جديدّْ؟, لم أعثر عليهْ")

                        app_state["mic_status"] = "listening" 
                    except Exception as ex:
                        add_log(f"⚠️ خطأ في التنفيذ: {ex}", "red"); app_state["mic_status"] = "listening"
                    finally:
                        app_state["voice_mode"] = False
            
            except Exception as loop_err:
                pass
            
            time.sleep(0.1)

    # --- معالجة الإغلاق الآمن ---
    threading.Thread(target=app_loop, daemon=True).start()

def main(page: ft.Page):
    try:
        main_app(page)

    except Exception as e:
        import traceback
        page.clean()
        page.add(
            ft.Text("⚠️ حدث خطأ أثناء تشغيل التطبيق:", color="red", weight="bold", size=20),
            ft.Text(f"{e}", color="red", weight="bold"),
            ft.Text(f"{traceback.format_exc()}", color="red", size=12, selectable=True)
        )
        page.update()

ft.app(target=main)