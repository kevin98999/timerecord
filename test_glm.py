import os
import requests

api_key = os.getenv("ZAI_API_KEY")

if not api_key:
    raise RuntimeError(
        "没有找到 ZAI_API_KEY。请先在 PowerShell 中设置环境变量。"
    )

url = "https://api.z.ai/api/paas/v4/chat/completions"

headers = {
    "Authorization": f"Bearer {api_key}",
    "Content-Type": "application/json",
}

data = {
    "model": "glm-5",
    "messages": [
        {
            "role": "user",
            "content": "你好，请用中文简单介绍一下自己。",
        }
    ],
    "stream": False,
}

try:
    response = requests.post(
        url,
        headers=headers,
        json=data,
        timeout=120,
    )

    response.raise_for_status()
    result = response.json()

    print(result["choices"][0]["message"]["content"])

except requests.HTTPError:
    print("API 请求失败：", response.status_code)
    print(response.text)

except requests.RequestException as error:
    print("网络连接错误：", error)

except (KeyError, IndexError, ValueError) as error:
    print("返回数据格式异常：", error)