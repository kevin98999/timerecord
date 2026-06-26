from PIL import Image, ImageDraw, ImageFont
from pathlib import Path
import textwrap


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT / "hosting-recommendations.pdf"

PAGE_W, PAGE_H = 1240, 1754
MARGIN_X = 90
MARGIN_Y = 80
LINE_GAP = 10


def font(size, bold=False):
    candidates = [
        Path("C:/Windows/Fonts/msyhbd.ttc" if bold else "C:/Windows/Fonts/msyh.ttc"),
        Path("C:/Windows/Fonts/simhei.ttf"),
        Path("C:/Windows/Fonts/simsun.ttc"),
        Path("C:/Windows/Fonts/arial.ttf"),
    ]
    for path in candidates:
        if path.exists():
            return ImageFont.truetype(str(path), size)
    return ImageFont.load_default()


F_TITLE = font(42, True)
F_H2 = font(28, True)
F_H3 = font(22, True)
F_BODY = font(20)
F_BODY_BOLD = font(20, True)
F_SMALL = font(16)


class PdfCanvas:
    def __init__(self):
        self.pages = []
        self.new_page()

    def new_page(self):
        self.img = Image.new("RGB", (PAGE_W, PAGE_H), "white")
        self.draw = ImageDraw.Draw(self.img)
        self.x = MARGIN_X
        self.y = MARGIN_Y
        self.pages.append(self.img)

    def ensure(self, height):
        if self.y + height > PAGE_H - MARGIN_Y:
            self.new_page()

    def text_size(self, text, fnt):
        box = self.draw.textbbox((0, 0), text, font=fnt)
        return box[2] - box[0], box[3] - box[1]

    def wrap(self, text, fnt, max_width):
        lines = []
        current = ""
        for ch in text:
            test = current + ch
            if self.text_size(test, fnt)[0] <= max_width:
                current = test
            else:
                if current:
                    lines.append(current)
                current = ch
        if current:
            lines.append(current)
        return lines

    def paragraph(self, text, fnt=F_BODY, color="#1f2933", width=None, indent=0, gap=LINE_GAP):
        width = width or (PAGE_W - 2 * MARGIN_X - indent)
        lines = self.wrap(text, fnt, width)
        line_h = self.text_size("测试", fnt)[1] + 12
        self.ensure(line_h * len(lines) + gap)
        for line in lines:
            self.draw.text((self.x + indent, self.y), line, font=fnt, fill=color)
            self.y += line_h
        self.y += gap

    def heading(self, text):
        self.ensure(52)
        self.draw.text((self.x, self.y), text, font=F_H2, fill="#243b53")
        self.y += 42
        self.draw.line((self.x, self.y, PAGE_W - MARGIN_X, self.y), fill="#cbd5e1", width=2)
        self.y += 18

    def bullet(self, text):
        self.ensure(44)
        bullet_x = self.x + 10
        text_x = self.x + 36
        self.draw.ellipse((bullet_x, self.y + 12, bullet_x + 8, self.y + 20), fill="#2f80ed")
        old_x = self.x
        self.x = text_x
        self.paragraph(text, F_BODY, width=PAGE_W - MARGIN_X - text_x, gap=4)
        self.x = old_x

    def callout(self, text):
        max_w = PAGE_W - 2 * MARGIN_X - 36
        lines = self.wrap(text, F_BODY, max_w)
        line_h = self.text_size("测试", F_BODY)[1] + 12
        box_h = line_h * len(lines) + 34
        self.ensure(box_h + 16)
        x0, y0 = self.x, self.y
        x1, y1 = PAGE_W - MARGIN_X, self.y + box_h
        self.draw.rectangle((x0, y0, x1, y1), fill="#fff7e6", outline="#f0c36d", width=2)
        yy = y0 + 16
        for line in lines:
            self.draw.text((x0 + 18, yy), line, font=F_BODY, fill="#1f2933")
            yy += line_h
        self.y = y1 + 16


def render():
    c = PdfCanvas()

    c.draw.text((MARGIN_X, c.y), "网页托管服务商推荐与价格对比", font=F_TITLE, fill="#102a43")
    c.y += 60
    c.paragraph("整理日期：2026-06-23。适用场景：将本地生成的静态网页、前端单页应用或轻量 Web 项目迁移到第三方托管平台。", F_SMALL, "#627d98")
    c.callout("结论：如果只是托管静态网页，优先选 Cloudflare Pages；如果是 React 或 Next.js 项目，优先选 Vercel；如果希望部署流程简单且带表单等网站功能，可以选 Netlify；如果项目已在 GitHub 且追求最低成本，可选 GitHub Pages。")

    c.heading("推荐服务商")
    items = [
        ("Cloudflare Pages", "静态网页、前端单页应用、需要全球 CDN、免费额度较宽的项目。Free 计划可用；官方限制页显示免费计划每月 500 次构建、每项目最多 100 个自定义域名、单站最多 20,000 文件。建议作为静态网页托管首选。"),
        ("Vercel", "React、Next.js、需要预览部署、自动 CI/CD 的前端项目。Hobby 免费；Pro 官方标价为 $20/月，且可能按额外使用量计费。前端框架项目体验最好。"),
        ("Netlify", "静态站、表单、Git 自动部署、非复杂后端项目。有免费计划；付费计划适合更高用量和团队协作。具体额度按官方 pricing 页面为准。适合内容站、小型企业官网。"),
        ("GitHub Pages", "公共仓库、项目文档、纯 HTML/CSS/JS 页面。GitHub Pages 是静态站托管服务，通常可免费用于公共仓库和项目页面；可绑定自定义域名。最低成本，但功能最简单。"),
        ("Render Static Sites", "静态站，同时未来可能部署后端服务、数据库或 API。Render pricing 页面显示 Hobby $0/月，Pro $25/月起；Web Services 另有实例计费。适合后续扩展到全栈部署。"),
        ("Firebase Hosting", "需要接 Firebase 登录、数据库、云函数、Google 生态服务。Spark 免费计划；Blaze 按量付费。Firebase pricing 页面显示 App Hosting 在 Blaze 下有免费额度后按流量和存储计费。适合未来要做用户系统或数据功能。"),
    ]
    for name, desc in items:
        c.ensure(90)
        c.draw.text((c.x, c.y), name, font=F_H3, fill="#334e68")
        c.y += 34
        c.paragraph(desc, F_BODY, gap=10)

    c.heading("按需求选择")
    choices = [
        "只托管静态网页：Cloudflare Pages。免费额度大、速度好、自定义域名方便。",
        "React / Next.js 项目：Vercel。部署体验和预览链接最成熟。",
        "需要表单、CMS 或站点工作流：Netlify。对营销页、展示站比较友好。",
        "项目已经在 GitHub，预算最低：GitHub Pages。适合纯静态页面和文档。",
        "后续可能加后端/API：Render 或 Firebase。Render 更通用，Firebase 更偏 Google 生态。",
    ]
    for choice in choices:
        c.bullet(choice)

    c.callout("额外费用提醒：如果要使用自己的域名，通常还需要购买域名。常见 .com 域名大约每年 $10-20，具体价格取决于注册商和促销活动。托管平台大多会免费提供 SSL 证书。")

    c.heading("推荐优先级")
    priorities = [
        "1. Cloudflare Pages：默认首选，适合绝大多数静态网页迁移。",
        "2. Vercel：如果项目是 Next.js 或现代前端框架，优先考虑。",
        "3. Netlify：如果看重站点功能、表单和易用控制台，可以选择。",
        "4. GitHub Pages：如果只要免费、简单、公开仓库部署，够用。",
        "5. Render / Firebase：当网站未来要扩展后端能力时再考虑。",
    ]
    for line in priorities:
        c.paragraph(line, F_BODY, gap=2)

    c.heading("资料来源")
    sources = [
        "Vercel Pricing: https://vercel.com/pricing",
        "Netlify Pricing: https://www.netlify.com/pricing/",
        "Cloudflare Pages Limits: https://developers.cloudflare.com/pages/platform/limits/",
        "Cloudflare Plans: https://www.cloudflare.com/plans/application-services/",
        "GitHub Pages Docs: https://docs.github.com/en/pages/getting-started-with-github-pages/what-is-github-pages",
        "Render Pricing: https://render.com/pricing",
        "Firebase Pricing: https://firebase.google.com/pricing",
    ]
    for source in sources:
        c.paragraph(source, F_SMALL, "#486581", gap=2)

    c.pages[0].save(OUTPUT, "PDF", resolution=150.0, save_all=True, append_images=c.pages[1:])


if __name__ == "__main__":
    render()
    print(OUTPUT)
