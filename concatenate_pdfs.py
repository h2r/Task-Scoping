from pypdf import PdfMerger
import os

pdfs_dir = "pdfs"
nms_resubmission = ["scoping_ijcai_2023_cover_letter.pdf", "Scoping_IJCAI_2022.pdf", "Scoping_IJCAI_2022 Supplement.pdf", "scoping_ijcai_2022_reviews.pdf"]

output_pth = os.path.join(pdfs_dir,"gen","resubmission.pdf")
m = PdfMerger()
for nm in nms_resubmission:
    m.append(os.path.join(pdfs_dir, nm))
m.write(output_pth)